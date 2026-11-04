import RMod.BrundanEllis.StackingReferenceHexagonAtoms556
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn556
open Superfusion

theorem assocBAC_alias : HexagonAtoms556.assocBAC = HexagonAtoms556.assocABC :=
  HexagonAtoms556.assocBAC_eq.symm.trans HexagonAtoms556.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms556.innerRightBAC = HexagonAtoms556.innerRightABC :=
  HexagonAtoms556.innerRightBAC_eq.symm.trans HexagonAtoms556.innerRightABC_eq

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

def rows_outerABC (r : LeftIndex 5 6 5) : List ℤ := rows_outerABCData.getD (leftPosition 5 6 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 5 6 5) : (tripleIndices 2 8 1).map ((HexagonAtoms556.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_2_0
  · exact rows_outerABC_eq_0_3_0
  · exact rows_outerABC_eq_0_4_0
  · exact rows_outerABC_eq_0_5_0
  · exact rows_outerABC_eq_0_6_0
  · exact rows_outerABC_eq_0_7_0
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_2_0
  · exact rows_outerABC_eq_1_3_0
  · exact rows_outerABC_eq_1_4_0
  · exact rows_outerABC_eq_1_5_0
  · exact rows_outerABC_eq_1_6_0
  · exact rows_outerABC_eq_1_7_0

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 19420960,
    decodeIntegerRow 16 3 1 20448832,
    decodeIntegerRow 16 3 1 20445880,
    decodeIntegerRow 16 3 1 23620000,
    decodeIntegerRow 16 3 1 2627360,
    decodeIntegerRow 16 3 1 31207232,
    decodeIntegerRow 16 3 1 11839160,
    decodeIntegerRow 16 3 1 2628000,
    decodeIntegerRow 16 3 1 2155616,
    decodeIntegerRow 16 3 1 30971360,
    decodeIntegerRow 16 3 1 30971040,
    decodeIntegerRow 16 3 1 40891760,
    decodeIntegerRow 16 3 1 23672416,
    decodeIntegerRow 16 3 1 22574560,
    decodeIntegerRow 16 3 1 20475040,
    decodeIntegerRow 16 3 1 23678320]

def rows_assocABC (r : RightIndex 5 5 6) : List ℤ := rows_assocABCData.getD (rightPosition 5 5 6 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 5 5 6) : (tripleIndices 4 4 1).map ((HexagonAtoms556.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_2_0
  · exact rows_assocABC_eq_0_3_0
  · exact rows_assocABC_eq_0_4_0
  · exact rows_assocABC_eq_0_5_0
  · exact rows_assocABC_eq_0_6_0
  · exact rows_assocABC_eq_0_7_0
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_1_0
  · exact rows_assocABC_eq_1_2_0
  · exact rows_assocABC_eq_1_3_0
  · exact rows_assocABC_eq_1_4_0
  · exact rows_assocABC_eq_1_5_0
  · exact rows_assocABC_eq_1_6_0
  · exact rows_assocABC_eq_1_7_0

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21517042,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 23117684,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21516556]

def rows_inverseACB (r : LeftIndex 5 6 5) : List ℤ := rows_inverseACBData.getD (leftPosition 5 6 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 6 5) : (tripleIndices 2 8 1).map ((HexagonAtoms556.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_4_0
  · exact rows_inverseACB_eq_0_5_0
  · exact rows_inverseACB_eq_0_6_0
  · exact rows_inverseACB_eq_0_7_0
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_4_0
  · exact rows_inverseACB_eq_1_5_0
  · exact rows_inverseACB_eq_1_6_0
  · exact rows_inverseACB_eq_1_7_0

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21701236,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21503758,
    decodeIntegerRow 16 3 1 16740364,
    decodeIntegerRow 16 3 1 7174462,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 26306302,
    decodeIntegerRow 16 3 1 22054804,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 21462124,
    decodeIntegerRow 16 3 1 21699778,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678]

def rows_assocBCA (r : RightIndex 5 6 5) : List ℤ := rows_assocBCAData.getD (rightPosition 5 6 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 5 6 5) : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_4_0
  · exact rows_assocBCA_eq_0_5_0
  · exact rows_assocBCA_eq_0_6_0
  · exact rows_assocBCA_eq_0_7_0
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_2_0
  · exact rows_assocBCA_eq_1_3_0
  · exact rows_assocBCA_eq_1_4_0
  · exact rows_assocBCA_eq_1_5_0
  · exact rows_assocBCA_eq_1_6_0
  · exact rows_assocBCA_eq_1_7_0

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 37466620,
    decodeIntegerRow 16 3 1 25774896,
    decodeIntegerRow 16 3 1 21363952,
    decodeIntegerRow 16 3 1 21456940,
    decodeIntegerRow 16 3 1 37466560,
    decodeIntegerRow 16 3 1 17271840,
    decodeIntegerRow 16 3 1 21678880,
    decodeIntegerRow 16 3 1 21458560,
    decodeIntegerRow 16 3 1 21328960,
    decodeIntegerRow 16 3 1 21575200,
    decodeIntegerRow 16 3 1 8768800,
    decodeIntegerRow 16 3 1 26837760,
    decodeIntegerRow 16 3 1 21722620,
    decodeIntegerRow 16 3 1 21576496,
    decodeIntegerRow 16 3 1 8768752,
    decodeIntegerRow 16 3 1 16208940]

def rows_assocCAB (r : RightIndex 6 5 5) : List ℤ := rows_assocCABData.getD (rightPosition 6 5 5 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 5 5) : (tripleIndices 2 8 1).map ((HexagonAtoms556.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_2_0
  · exact rows_assocCAB_eq_2_3_0
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_2_0
  · exact rows_assocCAB_eq_3_3_0

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21666568,
    decodeIntegerRow 16 3 1 21743356,
    decodeIntegerRow 16 3 1 41718152,
    decodeIntegerRow 16 3 1 28963556,
    decodeIntegerRow 16 3 1 21749512,
    decodeIntegerRow 16 3 1 21668836,
    decodeIntegerRow 16 3 1 28963512,
    decodeIntegerRow 16 3 1 41718084,
    decodeIntegerRow 16 3 1 33215048,
    decodeIntegerRow 16 3 1 39592316,
    decodeIntegerRow 16 3 1 21775432,
    decodeIntegerRow 16 3 1 21616996,
    decodeIntegerRow 16 3 1 39592392,
    decodeIntegerRow 16 3 1 33215076,
    decodeIntegerRow 16 3 1 21613432,
    decodeIntegerRow 16 3 1 21769924]

def cols_assocABC (r : LeftIndex 5 5 6) : List ℤ := cols_assocABCData.getD (leftPosition 5 5 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 5 6) : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms556.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_2_0
  · exact cols_assocABC_eq_1_3_0
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_2_0
  · exact cols_assocABC_eq_2_3_0
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_2_0
  · exact cols_assocABC_eq_3_3_0

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 22615384,
    decodeIntegerRow 16 3 1 19412212,
    decodeIntegerRow 16 3 1 2273544,
    decodeIntegerRow 16 3 1 12193292,
    decodeIntegerRow 16 3 1 23637496,
    decodeIntegerRow 16 3 1 22609588,
    decodeIntegerRow 16 3 1 12193944,
    decodeIntegerRow 16 3 1 40773492,
    decodeIntegerRow 16 3 1 11720904,
    decodeIntegerRow 16 3 1 40536972,
    decodeIntegerRow 16 3 1 19385896,
    decodeIntegerRow 16 3 1 20483788,
    decodeIntegerRow 16 3 1 40537304,
    decodeIntegerRow 16 3 1 31325172,
    decodeIntegerRow 16 3 1 22557064,
    decodeIntegerRow 16 3 1 19383052]

def cols_innerABC (r : LeftIndex 5 5 6) : List ℤ := cols_innerABCData.getD (leftPosition 5 5 6 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 5 5 6) : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms556.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_2_0
  · exact cols_innerABC_eq_0_3_0
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_2_0
  · exact cols_innerABC_eq_1_3_0
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_1_0
  · exact cols_innerABC_eq_2_2_0
  · exact cols_innerABC_eq_2_3_0
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_1_0
  · exact cols_innerABC_eq_3_2_0
  · exact cols_innerABC_eq_3_3_0

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21666568,
    decodeIntegerRow 16 3 1 21743356,
    decodeIntegerRow 16 3 1 41718152,
    decodeIntegerRow 16 3 1 28963556,
    decodeIntegerRow 16 3 1 21749512,
    decodeIntegerRow 16 3 1 21668836,
    decodeIntegerRow 16 3 1 28963512,
    decodeIntegerRow 16 3 1 41718084,
    decodeIntegerRow 16 3 1 33215048,
    decodeIntegerRow 16 3 1 39592316,
    decodeIntegerRow 16 3 1 21775432,
    decodeIntegerRow 16 3 1 21616996,
    decodeIntegerRow 16 3 1 39592392,
    decodeIntegerRow 16 3 1 33215076,
    decodeIntegerRow 16 3 1 21613432,
    decodeIntegerRow 16 3 1 21769924]

def cols_right0 (r : LeftIndex 5 5 6) : List ℤ := cols_right0Data.getD (leftPosition 5 5 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 5 6) : (tripleIndices 2 8 1).map (fun j => (right0Middle5 5 6) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_2_0
  · exact cols_right0_eq_2_3_0
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_2_0
  · exact cols_right0_eq_3_3_0

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21377884,
    decodeIntegerRow 16 3 1 21297208,
    decodeIntegerRow 16 3 1 1328636,
    decodeIntegerRow 16 3 1 14083208,
    decodeIntegerRow 16 3 1 21303364,
    decodeIntegerRow 16 3 1 21380152,
    decodeIntegerRow 16 3 1 14083164,
    decodeIntegerRow 16 3 1 1328568,
    decodeIntegerRow 16 3 1 9831644,
    decodeIntegerRow 16 3 1 3454328,
    decodeIntegerRow 16 3 1 21276796,
    decodeIntegerRow 16 3 1 21433288,
    decodeIntegerRow 16 3 1 3454404,
    decodeIntegerRow 16 3 1 9831672,
    decodeIntegerRow 16 3 1 21429724,
    decodeIntegerRow 16 3 1 21271288]

def cols_left0 (r : LeftIndex 5 5 6) : List ℤ := cols_left0Data.getD (leftPosition 5 5 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 5 6) : (tripleIndices 2 8 1).map (fun j => (left0Middle5 5 6) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_2_0
  · exact cols_left0_eq_2_3_0
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_2_0
  · exact cols_left0_eq_3_3_0

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 12817382552,
    decodeIntegerRow 16 5 2 64575195264,
    decodeIntegerRow 16 5 2 76387845312,
    decodeIntegerRow 16 5 2 76314290312,
    decodeIntegerRow 16 5 2 12817383072,
    decodeIntegerRow 16 5 2 88012695264,
    decodeIntegerRow 16 5 2 76200345312,
    decodeIntegerRow 16 5 2 76314225312,
    decodeIntegerRow 16 5 2 76395345312,
    decodeIntegerRow 16 5 2 76275225312,
    decodeIntegerRow 16 5 2 134887695072,
    decodeIntegerRow 16 5 2 63598632864,
    decodeIntegerRow 16 5 2 76192220312,
    decodeIntegerRow 16 5 2 76275165312,
    decodeIntegerRow 16 5 2 134887695552,
    decodeIntegerRow 16 5 2 88989257864]

def cols_right2 (r : LeftIndex 5 5 6) : List ℤ := cols_right2Data.getD (leftPosition 5 5 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 5 6) : (tripleIndices 2 8 1).map (fun j => (right2Middle5 5 6) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_2_0
  · exact cols_right2_eq_2_3_0
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_2_0
  · exact cols_right2_eq_3_3_0

theorem product0_eq : HexagonAtoms556.outerABC * HexagonAtoms556.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms556.assocABC * HexagonAtoms556.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms556.innerRightABC * HexagonAtoms556.assocABC = HexagonAtoms556.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 4 × Fin 4 × Fin 1) _

theorem product3_eq : HexagonAtoms556.inverseACB * right0Middle5 5 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms556.innerACB * right1Middle5 5 6 = right1Middle5 5 6 :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 4 × Fin 4 × Fin 1) _

theorem product5_eq : HexagonAtoms556.assocBCA * left0Middle5 5 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms556.innerRightABC * left1Middle5 5 6 = left1Middle5 5 6 :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 4 × Fin 4 × Fin 1) _

theorem product7_eq : HexagonAtoms556.assocCAB * right2Middle5 5 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn556
