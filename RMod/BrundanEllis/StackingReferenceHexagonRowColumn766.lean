import RMod.BrundanEllis.StackingReferenceHexagonAtoms766
import RMod.BrundanEllis.StackingReferenceHexagonMiddle7
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn766
open Superfusion

theorem innerACB_alias : HexagonAtoms766.innerACB = HexagonAtoms766.innerABC :=
  HexagonAtoms766.innerACB_eq.symm.trans HexagonAtoms766.innerABC_eq

theorem assocCAB_alias : HexagonAtoms766.assocCAB = HexagonAtoms766.assocBAC :=
  HexagonAtoms766.assocCAB_eq.symm.trans HexagonAtoms766.assocBAC_eq

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

def rows_assocBAC (r : RightIndex 6 7 6) : List ℤ := rows_assocBACData.getD (rightPosition 6 7 6 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocBAC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 6 7 6) : (tripleIndices 1 2 8).map ((HexagonAtoms766.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_0_4
  · exact rows_assocBAC_eq_0_0_5
  · exact rows_assocBAC_eq_0_0_6
  · exact rows_assocBAC_eq_0_0_7
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_0_1_4
  · exact rows_assocBAC_eq_0_1_5
  · exact rows_assocBAC_eq_0_1_6
  · exact rows_assocBAC_eq_0_1_7

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21464311]

def rows_innerRightABC (r : RightIndex 7 6 6) : List ℤ := rows_innerRightABCData.getD (rightPosition 7 6 6 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 7 6 6) : (tripleIndices 2 1 8).map ((HexagonAtoms766.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_0_4
  · exact rows_innerRightABC_eq_0_0_5
  · exact rows_innerRightABC_eq_0_0_6
  · exact rows_innerRightABC_eq_0_0_7
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_1_0_4
  · exact rows_innerRightABC_eq_1_0_5
  · exact rows_innerRightABC_eq_1_0_6
  · exact rows_innerRightABC_eq_1_0_7

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 7154986,
    decodeIntegerRow 16 3 1 26312962,
    decodeIntegerRow 16 3 1 19749706,
    decodeIntegerRow 16 3 1 22113122,
    decodeIntegerRow 16 3 1 20103994,
    decodeIntegerRow 16 3 1 21995022,
    decodeIntegerRow 16 3 1 7194406,
    decodeIntegerRow 16 3 1 26299858,
    decodeIntegerRow 16 3 1 16747042,
    decodeIntegerRow 16 3 1 7193866,
    decodeIntegerRow 16 3 1 21050238,
    decodeIntegerRow 16 3 1 20108374,
    decodeIntegerRow 16 3 1 22114578,
    decodeIntegerRow 16 3 1 23292646,
    decodeIntegerRow 16 3 1 26312818,
    decodeIntegerRow 16 3 1 35892166]

def rows_inverseACB (r : LeftIndex 7 6 6) : List ℤ := rows_inverseACBData.getD (leftPosition 7 6 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_inverseACB ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 7 6 6) : (tripleIndices 2 1 8).map ((HexagonAtoms766.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_0_0_4
  · exact rows_inverseACB_eq_0_0_5
  · exact rows_inverseACB_eq_0_0_6
  · exact rows_inverseACB_eq_0_0_7
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_1_2
  · exact rows_inverseACB_eq_0_1_3
  · exact rows_inverseACB_eq_0_1_4
  · exact rows_inverseACB_eq_0_1_5
  · exact rows_inverseACB_eq_0_1_6
  · exact rows_inverseACB_eq_0_1_7

private def rows_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21525472,
    decodeIntegerRow 16 3 1 21523872,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525460,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 35301460,
    decodeIntegerRow 16 3 1 36482440,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 36324976]

def rows_innerABC (r : LeftIndex 6 7 6) : List ℤ := rows_innerABCData.getD (leftPosition 6 7 6 r) []

private theorem rows_innerABC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerABC_data (r : LeftIndex 6 7 6) : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerABC) r) = rows_innerABC r := by
  fin_cases r
  · exact rows_innerABC_eq_0_0_0
  · exact rows_innerABC_eq_0_0_1
  · exact rows_innerABC_eq_0_0_2
  · exact rows_innerABC_eq_0_0_3
  · exact rows_innerABC_eq_0_0_4
  · exact rows_innerABC_eq_0_0_5
  · exact rows_innerABC_eq_0_0_6
  · exact rows_innerABC_eq_0_0_7
  · exact rows_innerABC_eq_0_1_0
  · exact rows_innerABC_eq_0_1_1
  · exact rows_innerABC_eq_0_1_2
  · exact rows_innerABC_eq_0_1_3
  · exact rows_innerABC_eq_0_1_4
  · exact rows_innerABC_eq_0_1_5
  · exact rows_innerABC_eq_0_1_6
  · exact rows_innerABC_eq_0_1_7

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 36403736,
    decodeIntegerRow 16 3 1 15146080,
    decodeIntegerRow 16 3 1 18334720,
    decodeIntegerRow 16 3 1 35340852,
    decodeIntegerRow 16 3 1 21341920,
    decodeIntegerRow 16 3 1 21603064,
    decodeIntegerRow 16 3 1 21563212,
    decodeIntegerRow 16 3 1 21354880,
    decodeIntegerRow 16 3 1 15146056,
    decodeIntegerRow 16 3 1 6643040,
    decodeIntegerRow 16 3 1 35340800,
    decodeIntegerRow 16 3 1 24712012,
    decodeIntegerRow 16 3 1 21601120,
    decodeIntegerRow 16 3 1 21709336,
    decodeIntegerRow 16 3 1 21350668,
    decodeIntegerRow 16 3 1 21484480]

def rows_assocBCA (r : RightIndex 6 6 7) : List ℤ := rows_assocBCAData.getD (rightPosition 6 6 7 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_4 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_5 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_6 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_7 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_4 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_5 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_6 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_7 : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_assocBCA ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 6 7) : (tripleIndices 2 1 8).map ((HexagonAtoms766.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_0_0_4
  · exact rows_assocBCA_eq_0_0_5
  · exact rows_assocBCA_eq_0_0_6
  · exact rows_assocBCA_eq_0_0_7
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_1_2
  · exact rows_assocBCA_eq_0_1_3
  · exact rows_assocBCA_eq_0_1_4
  · exact rows_assocBCA_eq_0_1_5
  · exact rows_assocBCA_eq_0_1_6
  · exact rows_assocBCA_eq_0_1_7

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21525472,
    decodeIntegerRow 16 3 1 21523872,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525460,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 35301460,
    decodeIntegerRow 16 3 1 36482440,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 36324976]

def rows_innerRightBAC (r : RightIndex 6 6 7) : List ℤ := rows_innerRightBACData.getD (rightPosition 6 6 7 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_4 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_5 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_6 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_7 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_4 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_5 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_6 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_7 : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = rows_innerRightBAC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 6 6 7) : (tripleIndices 1 2 8).map ((HexagonAtoms766.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_0_4
  · exact rows_innerRightBAC_eq_0_0_5
  · exact rows_innerRightBAC_eq_0_0_6
  · exact rows_innerRightBAC_eq_0_0_7
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_0_1_4
  · exact rows_innerRightBAC_eq_0_1_5
  · exact rows_innerRightBAC_eq_0_1_6
  · exact rows_innerRightBAC_eq_0_1_7

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21524306,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21521266,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21521242,
    decodeIntegerRow 16 3 1 21522846,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 7784626,
    decodeIntegerRow 16 3 1 6682378,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 35419558]

def cols_innerABC (r : LeftIndex 7 6 6) : List ℤ := cols_innerABCData.getD (leftPosition 7 6 6 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_innerABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 7 6 6) : (tripleIndices 1 2 8).map (fun j => (HexagonAtoms766.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_0_4
  · exact cols_innerABC_eq_0_0_5
  · exact cols_innerABC_eq_0_0_6
  · exact cols_innerABC_eq_0_0_7
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_1_2
  · exact cols_innerABC_eq_0_1_3
  · exact cols_innerABC_eq_0_1_4
  · exact cols_innerABC_eq_0_1_5
  · exact cols_innerABC_eq_0_1_6
  · exact cols_innerABC_eq_0_1_7

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 7154986,
    decodeIntegerRow 16 3 1 26312962,
    decodeIntegerRow 16 3 1 19749706,
    decodeIntegerRow 16 3 1 22113122,
    decodeIntegerRow 16 3 1 20103994,
    decodeIntegerRow 16 3 1 21995022,
    decodeIntegerRow 16 3 1 7194406,
    decodeIntegerRow 16 3 1 26299858,
    decodeIntegerRow 16 3 1 16747042,
    decodeIntegerRow 16 3 1 7193866,
    decodeIntegerRow 16 3 1 21050238,
    decodeIntegerRow 16 3 1 20108374,
    decodeIntegerRow 16 3 1 22114578,
    decodeIntegerRow 16 3 1 23292646,
    decodeIntegerRow 16 3 1 26312818,
    decodeIntegerRow 16 3 1 35892166]

def cols_assocABC (r : LeftIndex 7 6 6) : List ℤ := cols_assocABCData.getD (leftPosition 7 6 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_assocABC ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 7 6 6) : (tripleIndices 2 1 8).map (fun j => (HexagonAtoms766.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_0_4
  · exact cols_assocABC_eq_0_0_5
  · exact cols_assocABC_eq_0_0_6
  · exact cols_assocABC_eq_0_0_7
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_0_1_4
  · exact cols_assocABC_eq_0_1_5
  · exact cols_assocABC_eq_0_1_6
  · exact cols_assocABC_eq_0_1_7

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 20932140,
    decodeIntegerRow 16 3 1 23292640,
    decodeIntegerRow 16 3 1 26312800,
    decodeIntegerRow 16 3 1 7154500,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 35852368,
    decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 20104000,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 21996480,
    decodeIntegerRow 16 3 1 7193920,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 7155040,
    decodeIntegerRow 16 3 1 16733740,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 22113120]

def cols_right0 (r : LeftIndex 7 6 6) : List ℤ := cols_right0Data.getD (leftPosition 7 6 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 7 6 6) : (tripleIndices 2 1 8).map (fun j => (right0Middle7 6 6) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 75825201312,
    decodeIntegerRow 16 5 2 78637696512,
    decodeIntegerRow 16 5 2 88500039072,
    decodeIntegerRow 16 5 2 15262664064,
    decodeIntegerRow 16 5 2 88501601552,
    decodeIntegerRow 16 5 2 15254851560,
    decodeIntegerRow 16 5 2 75786139312,
    decodeIntegerRow 16 5 2 78833009112,
    decodeIntegerRow 16 5 2 78637694112,
    decodeIntegerRow 16 5 2 76762701312,
    decodeIntegerRow 16 5 2 15262726560,
    decodeIntegerRow 16 5 2 64087539072,
    decodeIntegerRow 16 5 2 15254914064,
    decodeIntegerRow 16 5 2 64085976552,
    decodeIntegerRow 16 5 2 78833006512,
    decodeIntegerRow 16 5 2 76801764312]

def cols_right1 (r : LeftIndex 7 6 6) : List ℤ := cols_right1Data.getD (leftPosition 7 6 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right1 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 7 6 6) : (tripleIndices 1 2 8).map (fun j => (right1Middle7 6 6) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_0_4
  · exact cols_right1_eq_0_0_5
  · exact cols_right1_eq_0_0_6
  · exact cols_right1_eq_0_0_7
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_1_2
  · exact cols_right1_eq_0_1_3
  · exact cols_right1_eq_0_1_4
  · exact cols_right1_eq_0_1_5
  · exact cols_right1_eq_0_1_6
  · exact cols_right1_eq_0_1_7

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7154986,
    decodeIntegerRow 16 3 1 26312962,
    decodeIntegerRow 16 3 1 19749706,
    decodeIntegerRow 16 3 1 22113122,
    decodeIntegerRow 16 3 1 20103994,
    decodeIntegerRow 16 3 1 21995022,
    decodeIntegerRow 16 3 1 7194406,
    decodeIntegerRow 16 3 1 26299858,
    decodeIntegerRow 16 3 1 16747042,
    decodeIntegerRow 16 3 1 7193866,
    decodeIntegerRow 16 3 1 21050238,
    decodeIntegerRow 16 3 1 20108374,
    decodeIntegerRow 16 3 1 22114578,
    decodeIntegerRow 16 3 1 23292646,
    decodeIntegerRow 16 3 1 26312818,
    decodeIntegerRow 16 3 1 35892166]

def cols_left0 (r : LeftIndex 7 6 6) : List ℤ := cols_left0Data.getD (leftPosition 7 6 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_4 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_5 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_6 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_7 : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_left0 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 7 6 6) : (tripleIndices 2 1 8).map (fun j => (left0Middle7 6 6) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 75825201312,
    decodeIntegerRow 16 5 2 78637696512,
    decodeIntegerRow 16 5 2 88500039072,
    decodeIntegerRow 16 5 2 15262664064,
    decodeIntegerRow 16 5 2 88501601552,
    decodeIntegerRow 16 5 2 15254851560,
    decodeIntegerRow 16 5 2 75786139312,
    decodeIntegerRow 16 5 2 78833009112,
    decodeIntegerRow 16 5 2 78637694112,
    decodeIntegerRow 16 5 2 76762701312,
    decodeIntegerRow 16 5 2 15262726560,
    decodeIntegerRow 16 5 2 64087539072,
    decodeIntegerRow 16 5 2 15254914064,
    decodeIntegerRow 16 5 2 64085976552,
    decodeIntegerRow 16 5 2 78833006512,
    decodeIntegerRow 16 5 2 76801764312]

def cols_left1 (r : LeftIndex 7 6 6) : List ℤ := cols_left1Data.getD (leftPosition 7 6 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_left1 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 7 6 6) : (tripleIndices 1 2 8).map (fun j => (left1Middle7 6 6) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_0_4
  · exact cols_left1_eq_0_0_5
  · exact cols_left1_eq_0_0_6
  · exact cols_left1_eq_0_0_7
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_1_2
  · exact cols_left1_eq_0_1_3
  · exact cols_left1_eq_0_1_4
  · exact cols_left1_eq_0_1_5
  · exact cols_left1_eq_0_1_6
  · exact cols_left1_eq_0_1_7

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 101815847898480,
    decodeIntegerRow 16 9 4 1028184727558720,
    decodeIntegerRow 16 9 4 1007849800932160,
    decodeIntegerRow 16 9 4 104075284190336,
    decodeIntegerRow 16 9 4 926635771693120,
    decodeIntegerRow 16 9 4 926494595244400,
    decodeIntegerRow 16 9 4 926497695080704,
    decodeIntegerRow 16 9 4 926635427371840,
    decodeIntegerRow 16 9 4 1028184727559440,
    decodeIntegerRow 16 9 4 1751204340947520,
    decodeIntegerRow 16 9 4 104075284196160,
    decodeIntegerRow 16 9 4 845170387919104,
    decodeIntegerRow 16 9 4 926494599968320,
    decodeIntegerRow 16 9 4 926384378842480,
    decodeIntegerRow 16 9 4 926635465583104,
    decodeIntegerRow 16 9 4 926522489992000]

def cols_right2 (r : LeftIndex 7 6 6) : List ℤ := cols_right2Data.getD (leftPosition 7 6 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_4 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_5 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_6 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_7 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_4 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_5 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_6 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_7 : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8))) = cols_right2 ((0 : Fin 1), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 7 6 6) : (tripleIndices 1 2 8).map (fun j => (right2Middle7 6 6) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms766.outerABC * HexagonAtoms766.assocABC = HexagonAtoms766.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 1 × Fin 8) (n := Fin 1 × Fin 2 × Fin 8) _

theorem product1_eq : HexagonAtoms766.assocBAC * HexagonAtoms766.innerABC = rowColumnMul rows_assocBAC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms766.innerRightABC * HexagonAtoms766.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms766.inverseACB * right0Middle7 6 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms766.innerABC * right1Middle7 6 6 = rowColumnMul rows_innerABC cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerABC_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms766.assocBCA * left0Middle7 6 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms766.innerRightBAC * left1Middle7 6 6 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms766.assocBAC * right2Middle7 6 6 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn766
