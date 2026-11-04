import RMod.BrundanEllis.StackingReferenceHexagonAtoms563
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn563
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425917,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094425893,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425191,
    decodeIntegerRow 32 3 1 926510094423733,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
    decodeIntegerRow 32 3 1 926510137472641,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510481846409,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926513581210321,
    decodeIntegerRow 32 3 1 926520554779123,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926792523962401,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 929051960254249,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 949386886880881,
    decodeIntegerRow 32 3 1 995140471790803,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 1544183490709867]

def rows_outerABC (r : LeftIndex 6 3 5) : List ℤ := rows_outerABCData.getD (leftPosition 6 3 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 6 3 5) : (tripleIndices 4 2 4).map ((HexagonAtoms563.outerABC) r) = rows_outerABC r := by
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
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_2_1_0
  · exact rows_outerABC_eq_2_1_1
  · exact rows_outerABC_eq_2_1_2
  · exact rows_outerABC_eq_2_1_3
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3
  · exact rows_outerABC_eq_3_1_0
  · exact rows_outerABC_eq_3_1_1
  · exact rows_outerABC_eq_3_1_2
  · exact rows_outerABC_eq_3_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 289439455219880,
    decodeIntegerRow 32 3 1 1056387059906272,
    decodeIntegerRow 32 3 1 659876824272040,
    decodeIntegerRow 32 3 1 333310960606368,
    decodeIntegerRow 32 3 1 1523099428558160,
    decodeIntegerRow 32 3 1 644058504169216,
    decodeIntegerRow 32 3 1 781949233429840,
    decodeIntegerRow 32 3 1 282661669284224,
    decodeIntegerRow 32 3 1 1570358526288080,
    decodeIntegerRow 32 3 1 781949203507456,
    decodeIntegerRow 32 3 1 1208961656973520,
    decodeIntegerRow 32 3 1 1523099415437184,
    decodeIntegerRow 32 3 1 333310948220120,
    decodeIntegerRow 32 3 1 1193143392131488,
    decodeIntegerRow 32 3 1 1056387030298840,
    decodeIntegerRow 32 3 1 1563580727593952,
    decodeIntegerRow 32 3 1 644102611725184,
    decodeIntegerRow 32 3 1 1522903122388400,
    decodeIntegerRow 32 3 1 282479833216256,
    decodeIntegerRow 32 3 1 781863110069680,
    decodeIntegerRow 32 3 1 796551886339552,
    decodeIntegerRow 32 3 1 1563761523824040,
    decodeIntegerRow 32 3 1 1519515013827488,
    decodeIntegerRow 32 3 1 1193103789152680,
    decodeIntegerRow 32 3 1 659916427259872,
    decodeIntegerRow 32 3 1 1519515001439400,
    decodeIntegerRow 32 3 1 289258658993568,
    decodeIntegerRow 32 3 1 796551856740520,
    decodeIntegerRow 32 3 1 781863139983616,
    decodeIntegerRow 32 3 1 1570540348919120,
    decodeIntegerRow 32 3 1 1522903135511424,
    decodeIntegerRow 32 3 1 1208917604844880]

def rows_inverseACB (r : LeftIndex 5 3 6) : List ℤ := rows_inverseACBData.getD (leftPosition 5 3 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 3 6) : (tripleIndices 4 2 4).map ((HexagonAtoms563.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_0_2
  · exact rows_inverseACB_eq_0_0_3
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_0_2
  · exact rows_inverseACB_eq_1_0_3
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_4_0_0
  · exact rows_inverseACB_eq_4_0_1
  · exact rows_inverseACB_eq_4_0_2
  · exact rows_inverseACB_eq_4_0_3
  · exact rows_inverseACB_eq_5_0_0
  · exact rows_inverseACB_eq_5_0_1
  · exact rows_inverseACB_eq_5_0_2
  · exact rows_inverseACB_eq_5_0_3
  · exact rows_inverseACB_eq_6_0_0
  · exact rows_inverseACB_eq_6_0_1
  · exact rows_inverseACB_eq_6_0_2
  · exact rows_inverseACB_eq_6_0_3
  · exact rows_inverseACB_eq_7_0_0
  · exact rows_inverseACB_eq_7_0_1
  · exact rows_inverseACB_eq_7_0_2
  · exact rows_inverseACB_eq_7_0_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 1563580727593952,
    decodeIntegerRow 32 3 1 796633158553000,
    decodeIntegerRow 32 3 1 1193143392131488,
    decodeIntegerRow 32 3 1 1519709240631720,
    decodeIntegerRow 32 3 1 329920773414656,
    decodeIntegerRow 32 3 1 1208961656973520,
    decodeIntegerRow 32 3 1 1071070985344384,
    decodeIntegerRow 32 3 1 1570358526288080,
    decodeIntegerRow 32 3 1 282661669284224,
    decodeIntegerRow 32 3 1 1071070955422000,
    decodeIntegerRow 32 3 1 644058504169216,
    decodeIntegerRow 32 3 1 329920760293680,
    decodeIntegerRow 32 3 1 1519709228245472,
    decodeIntegerRow 32 3 1 659876824272040,
    decodeIntegerRow 32 3 1 796633128945568,
    decodeIntegerRow 32 3 1 289439455219880,
    decodeIntegerRow 32 3 1 1208917604844880,
    decodeIntegerRow 32 3 1 330117053340416,
    decodeIntegerRow 32 3 1 1570540348919120,
    decodeIntegerRow 32 3 1 1071157048868224,
    decodeIntegerRow 32 3 1 1056468332111320,
    decodeIntegerRow 32 3 1 289258658993568,
    decodeIntegerRow 32 3 1 333505187412440,
    decodeIntegerRow 32 3 1 659916427259872,
    decodeIntegerRow 32 3 1 1193103789152680,
    decodeIntegerRow 32 3 1 333505175024352,
    decodeIntegerRow 32 3 1 1563761523824040,
    decodeIntegerRow 32 3 1 1056468302512288,
    decodeIntegerRow 32 3 1 1071157078782160,
    decodeIntegerRow 32 3 1 282479833216256,
    decodeIntegerRow 32 3 1 330117066463440,
    decodeIntegerRow 32 3 1 644102611725184]

def rows_assocBCA (r : RightIndex 6 3 5) : List ℤ := rows_assocBCAData.getD (rightPosition 6 3 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 3 5) : (tripleIndices 4 2 4).map ((HexagonAtoms563.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_0_2
  · exact rows_assocBCA_eq_0_0_3
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_0_2
  · exact rows_assocBCA_eq_1_0_3
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_4_0_0
  · exact rows_assocBCA_eq_4_0_1
  · exact rows_assocBCA_eq_4_0_2
  · exact rows_assocBCA_eq_4_0_3
  · exact rows_assocBCA_eq_5_0_0
  · exact rows_assocBCA_eq_5_0_1
  · exact rows_assocBCA_eq_5_0_2
  · exact rows_assocBCA_eq_5_0_3
  · exact rows_assocBCA_eq_6_0_0
  · exact rows_assocBCA_eq_6_0_1
  · exact rows_assocBCA_eq_6_0_2
  · exact rows_assocBCA_eq_6_0_3
  · exact rows_assocBCA_eq_7_0_0
  · exact rows_assocBCA_eq_7_0_1
  · exact rows_assocBCA_eq_7_0_2
  · exact rows_assocBCA_eq_7_0_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 785902271320004,
    decodeIntegerRow 32 3 1 1574311595748172,
    decodeIntegerRow 32 3 1 1513495185250276,
    decodeIntegerRow 32 3 1 1199357445865388,
    decodeIntegerRow 32 3 1 785818099201244,
    decodeIntegerRow 32 3 1 1574495306477548,
    decodeIntegerRow 32 3 1 1513302157218556,
    decodeIntegerRow 32 3 1 1199316607472012,
    decodeIntegerRow 32 3 1 323706717508372,
    decodeIntegerRow 32 3 1 1202747603659556,
    decodeIntegerRow 32 3 1 1060340097586548,
    decodeIntegerRow 32 3 1 1559627657713924,
    decodeIntegerRow 32 3 1 323904209644492,
    decodeIntegerRow 32 3 1 1202704758544964,
    decodeIntegerRow 32 3 1 1060423291853868,
    decodeIntegerRow 32 3 1 1559806572719716,
    decodeIntegerRow 32 3 1 323706711286612,
    decodeIntegerRow 32 3 1 1202747633083236,
    decodeIntegerRow 32 3 1 1060340125584308,
    decodeIntegerRow 32 3 1 1559627670546244,
    decodeIntegerRow 32 3 1 1529115972989452,
    decodeIntegerRow 32 3 1 650315459722244,
    decodeIntegerRow 32 3 1 792596925004908,
    decodeIntegerRow 32 3 1 293213628966436,
    decodeIntegerRow 32 3 1 1067117890268804,
    decodeIntegerRow 32 3 1 278708605778572,
    decodeIntegerRow 32 3 1 339525010138276,
    decodeIntegerRow 32 3 1 653662773092588,
    decodeIntegerRow 32 3 1 785818071929244,
    decodeIntegerRow 32 3 1 1574495319154348,
    decodeIntegerRow 32 3 1 1513302163751356,
    decodeIntegerRow 32 3 1 1199316637569612]

def rows_assocCAB (r : RightIndex 3 5 6) : List ℤ := rows_assocCABData.getD (rightPosition 3 5 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_2 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_3 : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 5 6) : (tripleIndices 8 1 4).map ((HexagonAtoms563.assocCAB) r) = rows_assocCAB r := by
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
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_2_1
  · exact rows_assocCAB_eq_1_2_2
  · exact rows_assocCAB_eq_1_2_3
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_1_3_1
  · exact rows_assocCAB_eq_1_3_2
  · exact rows_assocCAB_eq_1_3_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 789207498204604,
    decodeIntegerRow 32 3 1 1567150939729868,
    decodeIntegerRow 32 3 1 1521209068107996,
    decodeIntegerRow 32 3 1 1201010683139692,
    decodeIntegerRow 32 3 1 1063729007821600,
    decodeIntegerRow 32 3 1 286050561910880,
    decodeIntegerRow 32 3 1 331615860817440,
    decodeIntegerRow 32 3 1 651967664299360,
    decodeIntegerRow 32 3 1 928204161460960,
    decodeIntegerRow 32 3 1 918603172804000,
    decodeIntegerRow 32 3 1 919165736051680,
    decodeIntegerRow 32 3 1 923120684897440,
    decodeIntegerRow 32 3 1 928205194583236,
    decodeIntegerRow 32 3 1 918600934369972,
    decodeIntegerRow 32 3 1 919168146663844,
    decodeIntegerRow 32 3 1 923121201456148,
    decodeIntegerRow 32 3 1 1521404328401868,
    decodeIntegerRow 32 3 1 651967664220604,
    decodeIntegerRow 32 3 1 789291181187692,
    decodeIntegerRow 32 3 1 286050562251996,
    decodeIntegerRow 32 3 1 331811120376480,
    decodeIntegerRow 32 3 1 1201010683218400,
    decodeIntegerRow 32 3 1 1063812690489760,
    decodeIntegerRow 32 3 1 1567150939388640,
    decodeIntegerRow 32 3 1 933852071944480,
    decodeIntegerRow 32 3 1 923121195080800,
    decodeIntegerRow 32 3 1 924815007024160,
    decodeIntegerRow 32 3 1 918600962009440,
    decodeIntegerRow 32 3 1 933854482565068,
    decodeIntegerRow 32 3 1 923120678518204,
    decodeIntegerRow 32 3 1 924816040144492,
    decodeIntegerRow 32 3 1 918603200434396]

def cols_assocABC (r : LeftIndex 5 6 3) : List ℤ := cols_assocABCData.getD (leftPosition 5 6 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 6 3) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms563.assocABC) j r) = cols_assocABC r := by
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
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_1_2_0
  · exact cols_assocABC_eq_1_2_1
  · exact cols_assocABC_eq_1_2_2
  · exact cols_assocABC_eq_1_2_3
  · exact cols_assocABC_eq_1_3_0
  · exact cols_assocABC_eq_1_3_1
  · exact cols_assocABC_eq_1_3_2
  · exact cols_assocABC_eq_1_3_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789207498204604,
    decodeIntegerRow 32 3 1 1567150939729868,
    decodeIntegerRow 32 3 1 1521209068107996,
    decodeIntegerRow 32 3 1 1201010683139692,
    decodeIntegerRow 32 3 1 1063729007821600,
    decodeIntegerRow 32 3 1 286050561910880,
    decodeIntegerRow 32 3 1 331615860817440,
    decodeIntegerRow 32 3 1 651967664299360,
    decodeIntegerRow 32 3 1 928204161460960,
    decodeIntegerRow 32 3 1 918603172804000,
    decodeIntegerRow 32 3 1 919165736051680,
    decodeIntegerRow 32 3 1 923120684897440,
    decodeIntegerRow 32 3 1 928205194583236,
    decodeIntegerRow 32 3 1 918600934369972,
    decodeIntegerRow 32 3 1 919168146663844,
    decodeIntegerRow 32 3 1 923121201456148,
    decodeIntegerRow 32 3 1 1521404328401868,
    decodeIntegerRow 32 3 1 651967664220604,
    decodeIntegerRow 32 3 1 789291181187692,
    decodeIntegerRow 32 3 1 286050562251996,
    decodeIntegerRow 32 3 1 331811120376480,
    decodeIntegerRow 32 3 1 1201010683218400,
    decodeIntegerRow 32 3 1 1063812690489760,
    decodeIntegerRow 32 3 1 1567150939388640,
    decodeIntegerRow 32 3 1 933852071944480,
    decodeIntegerRow 32 3 1 923121195080800,
    decodeIntegerRow 32 3 1 924815007024160,
    decodeIntegerRow 32 3 1 918600962009440,
    decodeIntegerRow 32 3 1 933854482565068,
    decodeIntegerRow 32 3 1 923120678518204,
    decodeIntegerRow 32 3 1 924816040144492,
    decodeIntegerRow 32 3 1 918603200434396]

def cols_right0 (r : LeftIndex 5 6 3) : List ℤ := cols_right0Data.getD (leftPosition 5 6 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 6 3) : (tripleIndices 4 2 4).map (fun j => (right0Middle5 6 3) j r) = cols_right0 r := by
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
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_2_1
  · exact cols_right0_eq_1_2_2
  · exact cols_right0_eq_1_2_3
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_1_3_1
  · exact cols_right0_eq_1_3_2
  · exact cols_right0_eq_1_3_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789207498362080,
    decodeIntegerRow 32 3 1 1567150939388640,
    decodeIntegerRow 32 3 1 1521209068475360,
    decodeIntegerRow 32 3 1 1201010683218400,
    decodeIntegerRow 32 3 1 1063729007664148,
    decodeIntegerRow 32 3 1 286050562251996,
    decodeIntegerRow 32 3 1 331615860449972,
    decodeIntegerRow 32 3 1 651967664220604,
    decodeIntegerRow 32 3 1 928204148707348,
    decodeIntegerRow 32 3 1 918603200434396,
    decodeIntegerRow 32 3 1 919165706286772,
    decodeIntegerRow 32 3 1 923120678518204,
    decodeIntegerRow 32 3 1 928205181827680,
    decodeIntegerRow 32 3 1 918600962009440,
    decodeIntegerRow 32 3 1 919168116907360,
    decodeIntegerRow 32 3 1 923121195080800,
    decodeIntegerRow 32 3 1 1521404328034400,
    decodeIntegerRow 32 3 1 651967664299360,
    decodeIntegerRow 32 3 1 789291181030240,
    decodeIntegerRow 32 3 1 286050561910880,
    decodeIntegerRow 32 3 1 331811120743844,
    decodeIntegerRow 32 3 1 1201010683139692,
    decodeIntegerRow 32 3 1 1063812690647236,
    decodeIntegerRow 32 3 1 1567150939729868,
    decodeIntegerRow 32 3 1 933852042187996,
    decodeIntegerRow 32 3 1 923121201456148,
    decodeIntegerRow 32 3 1 924814994268604,
    decodeIntegerRow 32 3 1 918600934369972,
    decodeIntegerRow 32 3 1 933854452800160,
    decodeIntegerRow 32 3 1 923120684897440,
    decodeIntegerRow 32 3 1 924816027390880,
    decodeIntegerRow 32 3 1 918603172804000]

def cols_left0 (r : LeftIndex 5 6 3) : List ℤ := cols_left0Data.getD (leftPosition 5 6 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 6 3) : (tripleIndices 4 2 4).map (fun j => (left0Middle5 6 3) j r) = cols_left0 r := by
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
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_2_1
  · exact cols_left0_eq_1_2_2
  · exact cols_left0_eq_1_2_3
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_1_3_1
  · exact cols_left0_eq_1_3_2
  · exact cols_left0_eq_1_3_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1719167899680411821917837571344,
    decodeIntegerRow 32 9 4 1735656581044760716524996368144,
    decodeIntegerRow 32 9 4 1886409418778222140253507025424,
    decodeIntegerRow 32 9 4 3242923324440012338064144350224,
    decodeIntegerRow 32 9 4 1719167899572343867515238480000,
    decodeIntegerRow 32 9 4 1735656580170607913425872356480,
    decodeIntegerRow 32 9 4 1886409410899921507339407644800,
    decodeIntegerRow 32 9 4 3242923253536522184642825495680,
    decodeIntegerRow 32 9 4 1886403667716153387712858576000,
    decodeIntegerRow 32 9 4 190759928624460488861529347200,
    decodeIntegerRow 32 9 4 1718702701687126177764763907200,
    decodeIntegerRow 32 9 4 1697975551467989867798942774400,
    decodeIntegerRow 32 9 4 1886403675594187190238635875216,
    decodeIntegerRow 32 9 4 190759857720940727787042116464,
    decodeIntegerRow 32 9 4 1718702701773580870713274404496,
    decodeIntegerRow 32 9 4 1697975550591438844793180291184,
    decodeIntegerRow 32 9 4 1886409410899921505331019876480,
    decodeIntegerRow 32 9 4 190760566755990279652203164800,
    decodeIntegerRow 32 9 4 1719167899572343684504002455680,
    decodeIntegerRow 32 9 4 1698027240121902924102613865600,
    decodeIntegerRow 32 9 4 1547274401514290342395954202224,
    decodeIntegerRow 32 9 4 3242923324440012317701322975344,
    decodeIntegerRow 32 9 4 1714515920612100479728766990704,
    decodeIntegerRow 32 9 4 1735656581044759069395556973424,
    decodeIntegerRow 32 9 4 1718702701773580687695831149296,
    decodeIntegerRow 32 9 4 1735708269701075286993419445264,
    decodeIntegerRow 32 9 4 1886403675594187187728151048176,
    decodeIntegerRow 32 9 4 3242923962571571777177839795984,
    decodeIntegerRow 32 9 4 1714981118605386123875650430080,
    decodeIntegerRow 32 9 4 1697975551467991514927616894080,
    decodeIntegerRow 32 9 4 1547280152576359094434505802880,
    decodeIntegerRow 32 9 4 190759928624460509168561226880]

def cols_right2 (r : LeftIndex 5 6 3) : List ℤ := cols_right2Data.getD (leftPosition 5 6 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 6 3) : (tripleIndices 8 1 4).map (fun j => (right2Middle5 6 3) j r) = cols_right2 r := by
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
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_2_1
  · exact cols_right2_eq_1_2_2
  · exact cols_right2_eq_1_2_3
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_1_3_1
  · exact cols_right2_eq_1_3_2
  · exact cols_right2_eq_1_3_3

theorem product0_eq : HexagonAtoms563.outerABC * HexagonAtoms563.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms563.assocBAC * HexagonAtoms563.innerABC = HexagonAtoms563.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product2_eq : HexagonAtoms563.innerRightABC * HexagonAtoms563.assocABC = HexagonAtoms563.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms563.inverseACB * right0Middle5 6 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms563.innerACB * right1Middle5 6 3 = right1Middle5 6 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product5_eq : HexagonAtoms563.assocBCA * left0Middle5 6 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms563.innerRightBAC * left1Middle5 6 3 = left1Middle5 6 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 2 × Fin 4 × Fin 4) _

theorem product7_eq : HexagonAtoms563.assocCAB * right2Middle5 6 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn563
