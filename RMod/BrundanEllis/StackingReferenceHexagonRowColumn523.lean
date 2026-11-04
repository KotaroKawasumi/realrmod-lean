import RMod.BrundanEllis.StackingReferenceHexagonAtoms523
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn523
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510079374020,
    decodeIntegerRow 32 3 1 926510088011504,
    decodeIntegerRow 32 3 1 926510091313872,
    decodeIntegerRow 32 3 1 926510080792660,
    decodeIntegerRow 32 3 1 926510080791664,
    decodeIntegerRow 32 3 1 926510091318140,
    decodeIntegerRow 32 3 1 926510100844820,
    decodeIntegerRow 32 3 1 926510109475888,
    decodeIntegerRow 32 3 1 926510097695376,
    decodeIntegerRow 32 3 1 926510080425220,
    decodeIntegerRow 32 3 1 926510079715180,
    decodeIntegerRow 32 3 1 926510100761552,
    decodeIntegerRow 32 3 1 926510088085700,
    decodeIntegerRow 32 3 1 926510109134704,
    decodeIntegerRow 32 3 1 926510080424272,
    decodeIntegerRow 32 3 1 926510097691220,
    decodeIntegerRow 32 3 1 1574445034245820,
    decodeIntegerRow 32 3 1 1202629670355856,
    decodeIntegerRow 32 3 1 1060473556420528,
    decodeIntegerRow 32 3 1 1513377233966380,
    decodeIntegerRow 32 3 1 1513420108500496,
    decodeIntegerRow 32 3 1 1060289833015300,
    decodeIntegerRow 32 3 1 650197496999020,
    decodeIntegerRow 32 3 1 278658320870992,
    decodeIntegerRow 32 3 1 785770734172144,
    decodeIntegerRow 32 3 1 1529194321130620,
    decodeIntegerRow 32 3 1 1559759214909460,
    decodeIntegerRow 32 3 1 653781911363248,
    decodeIntegerRow 32 3 1 1199435775844540,
    decodeIntegerRow 32 3 1 293345173328656,
    decodeIntegerRow 32 3 1 1529235129422128,
    decodeIntegerRow 32 3 1 785949636344620]

def rows_outerABC (r : LeftIndex 2 3 5) : List ℤ := rows_outerABCData.getD (leftPosition 2 3 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 2 3 5) : (tripleIndices 2 4 4).map ((HexagonAtoms523.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_0_2_0
  · exact rows_outerABC_eq_0_2_1
  · exact rows_outerABC_eq_0_2_2
  · exact rows_outerABC_eq_0_2_3
  · exact rows_outerABC_eq_0_3_0
  · exact rows_outerABC_eq_0_3_1
  · exact rows_outerABC_eq_0_3_2
  · exact rows_outerABC_eq_0_3_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3
  · exact rows_outerABC_eq_1_2_0
  · exact rows_outerABC_eq_1_2_1
  · exact rows_outerABC_eq_1_2_2
  · exact rows_outerABC_eq_1_2_3
  · exact rows_outerABC_eq_1_3_0
  · exact rows_outerABC_eq_1_3_1
  · exact rows_outerABC_eq_1_3_2
  · exact rows_outerABC_eq_1_3_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 926802984258742,
    decodeIntegerRow 32 3 1 927353896428838,
    decodeIntegerRow 32 3 1 929146103439394,
    decodeIntegerRow 32 3 1 934104310831534,
    decodeIntegerRow 32 3 1 934104310871062,
    decodeIntegerRow 32 3 1 929146103426758,
    decodeIntegerRow 32 3 1 925666292778754,
    decodeIntegerRow 32 3 1 926217204479374,
    decodeIntegerRow 32 3 1 1544183876536034,
    decodeIntegerRow 32 3 1 1132400064790546,
    decodeIntegerRow 32 3 1 857879659665418,
    decodeIntegerRow 32 3 1 903633435894118,
    decodeIntegerRow 32 3 1 949386762523714,
    decodeIntegerRow 32 3 1 995140500488626,
    decodeIntegerRow 32 3 1 1132400063727658,
    decodeIntegerRow 32 3 1 1544183879724678,
    decodeIntegerRow 32 3 1 925659319208494,
    decodeIntegerRow 32 3 1 926782063670434,
    decodeIntegerRow 32 3 1 918853115861722,
    decodeIntegerRow 32 3 1 928957817068618,
    decodeIntegerRow 32 3 1 924062371769614,
    decodeIntegerRow 32 3 1 934167072950914,
    decodeIntegerRow 32 3 1 926782063547962,
    decodeIntegerRow 32 3 1 925659318855658,
    decodeIntegerRow 32 3 1 1132402388250598,
    decodeIntegerRow 32 3 1 308837083968138,
    decodeIntegerRow 32 3 1 903633168047854,
    decodeIntegerRow 32 3 1 995140414395166,
    decodeIntegerRow 32 3 1 995140443092998,
    decodeIntegerRow 32 3 1 903633177613738,
    decodeIntegerRow 32 3 1 1544183101695054,
    decodeIntegerRow 32 3 1 720617799538366]

def rows_inverseACB (r : LeftIndex 5 3 2) : List ℤ := rows_inverseACBData.getD (leftPosition 5 3 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_4_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_5_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_6_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_7_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 3 2) : (tripleIndices 2 4 4).map ((HexagonAtoms523.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 929989890377764,
    decodeIntegerRow 32 3 1 918622981733592,
    decodeIntegerRow 32 3 1 933811417772996,
    decodeIntegerRow 32 3 1 924717873426328,
    decodeIntegerRow 32 3 1 924717901061284,
    decodeIntegerRow 32 3 1 933811424150232,
    decodeIntegerRow 32 3 1 934397194363716,
    decodeIntegerRow 32 3 1 923030268713368,
    decodeIntegerRow 32 3 1 929808607349608,
    decodeIntegerRow 32 3 1 918581153075364,
    decodeIntegerRow 32 3 1 933895106975912,
    decodeIntegerRow 32 3 1 924913160987716,
    decodeIntegerRow 32 3 1 928107055499032,
    decodeIntegerRow 32 3 1 919125088253276,
    decodeIntegerRow 32 3 1 918581140320728,
    decodeIntegerRow 32 3 1 929808577588924,
    decodeIntegerRow 32 3 1 1521307214857192,
    decodeIntegerRow 32 3 1 1063769643677884,
    decodeIntegerRow 32 3 1 651989703997912,
    decodeIntegerRow 32 3 1 285959647487524,
    decodeIntegerRow 32 3 1 1567060541525992,
    decodeIntegerRow 32 3 1 1201030484487484,
    decodeIntegerRow 32 3 1 1063769644017112,
    decodeIntegerRow 32 3 1 1521307214773924,
    decodeIntegerRow 32 3 1 331714007194684,
    decodeIntegerRow 32 3 1 789248134216408,
    decodeIntegerRow 32 3 1 1201032722916004,
    decodeIntegerRow 32 3 1 1567060024961128,
    decodeIntegerRow 32 3 1 1567060024807876,
    decodeIntegerRow 32 3 1 1201032723284392,
    decodeIntegerRow 32 3 1 1063772054292316,
    decodeIntegerRow 32 3 1 1521306181731352]

def rows_assocBCA (r : RightIndex 2 3 5) : List ℤ := rows_assocBCAData.getD (rightPosition 2 3 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_4_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_5_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_6_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_7_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocBCA ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 2 3 5) : (tripleIndices 2 4 4).map ((HexagonAtoms523.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 1060403145620864,
    decodeIntegerRow 32 3 1 339529659026200,
    decodeIntegerRow 32 3 1 278520220572400,
    decodeIntegerRow 32 3 1 1202767749183648,
    decodeIntegerRow 32 3 1 1529125277457040,
    decodeIntegerRow 32 3 1 1067139585448608,
    decodeIntegerRow 32 3 1 653725247170944,
    decodeIntegerRow 32 3 1 293401829150440,
    decodeIntegerRow 32 3 1 1202767779290000,
    decodeIntegerRow 32 3 1 278520233407648,
    decodeIntegerRow 32 3 1 1513490536046464,
    decodeIntegerRow 32 3 1 792617070502760,
    decodeIntegerRow 32 3 1 1559618372375296,
    decodeIntegerRow 32 3 1 1199294912265960,
    decodeIntegerRow 32 3 1 1067139613446800,
    decodeIntegerRow 32 3 1 1529125270923232,
    decodeIntegerRow 32 3 1 1559815870733200,
    decodeIntegerRow 32 3 1 1199379111647648,
    decodeIntegerRow 32 3 1 1067180421742464,
    decodeIntegerRow 32 3 1 1529304173094760,
    decodeIntegerRow 32 3 1 650335575831296,
    decodeIntegerRow 32 3 1 1574306933949160,
    decodeIntegerRow 32 3 1 339713376211600,
    decodeIntegerRow 32 3 1 1060360243819232,
    decodeIntegerRow 32 3 1 1529304179630464,
    decodeIntegerRow 32 3 1 1067180393735960,
    decodeIntegerRow 32 3 1 653641047780080,
    decodeIntegerRow 32 3 1 293204330796448,
    decodeIntegerRow 32 3 1 792659917769360,
    decodeIntegerRow 32 3 1 1513306806421408,
    decodeIntegerRow 32 3 1 1574306946780544,
    decodeIntegerRow 32 3 1 650335605928680]

def rows_assocCAB (r : RightIndex 3 5 2) : List ℤ := rows_assocCABData.getD (rightPosition 3 5 2 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 5 2) : (tripleIndices 8 1 4).map ((HexagonAtoms523.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_2_1_2
  · exact rows_assocCAB_eq_2_1_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1
  · exact rows_assocCAB_eq_3_1_2
  · exact rows_assocCAB_eq_3_1_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 293345176593956,
    decodeIntegerRow 32 3 1 653584399005652,
    decodeIntegerRow 32 3 1 785949621635836,
    decodeIntegerRow 32 3 1 323785065769932,
    decodeIntegerRow 32 3 1 785770748882884,
    decodeIntegerRow 32 3 1 1529194327466252,
    decodeIntegerRow 32 3 1 1559759218178916,
    decodeIntegerRow 32 3 1 653781925363948,
    decodeIntegerRow 32 3 1 323785053089492,
    decodeIntegerRow 32 3 1 785949651053404,
    decodeIntegerRow 32 3 1 1199435761842892,
    decodeIntegerRow 32 3 1 1559675018788484,
    decodeIntegerRow 32 3 1 653781897362548,
    decodeIntegerRow 32 3 1 1559759211640004,
    decodeIntegerRow 32 3 1 323825874056852,
    decodeIntegerRow 32 3 1 1067249469390436,
    decodeIntegerRow 32 3 1 1202822705487076,
    decodeIntegerRow 32 3 1 278658323978772,
    decodeIntegerRow 32 3 1 1513420102081596,
    decodeIntegerRow 32 3 1 792730340786572,
    decodeIntegerRow 32 3 1 339642948471044,
    decodeIntegerRow 32 3 1 792546647483212,
    decodeIntegerRow 32 3 1 1202629656722596,
    decodeIntegerRow 32 3 1 1574445037357868,
    decodeIntegerRow 32 3 1 1060289817965332,
    decodeIntegerRow 32 3 1 339600073932444,
    decodeIntegerRow 32 3 1 278658317763212,
    decodeIntegerRow 32 3 1 1202822678218564,
    decodeIntegerRow 32 3 1 278575157718068,
    decodeIntegerRow 32 3 1 650390504862724,
    decodeIntegerRow 32 3 1 792546617379412,
    decodeIntegerRow 32 3 1 339642961299876]

def cols_assocABC (r : LeftIndex 5 2 3) : List ℤ := cols_assocABCData.getD (leftPosition 5 2 3 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 2 3) : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms523.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_1_2
  · exact cols_assocABC_eq_0_1_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_1_2
  · exact cols_assocABC_eq_1_1_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_2_1_2
  · exact cols_assocABC_eq_2_1_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1
  · exact cols_assocABC_eq_3_1_2
  · exact cols_assocABC_eq_3_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 293345176593956,
    decodeIntegerRow 32 3 1 653584399005652,
    decodeIntegerRow 32 3 1 785949621635836,
    decodeIntegerRow 32 3 1 323785065769932,
    decodeIntegerRow 32 3 1 785770748882884,
    decodeIntegerRow 32 3 1 1529194327466252,
    decodeIntegerRow 32 3 1 1559759218178916,
    decodeIntegerRow 32 3 1 653781925363948,
    decodeIntegerRow 32 3 1 323785053089492,
    decodeIntegerRow 32 3 1 785949651053404,
    decodeIntegerRow 32 3 1 1199435761842892,
    decodeIntegerRow 32 3 1 1559675018788484,
    decodeIntegerRow 32 3 1 653781897362548,
    decodeIntegerRow 32 3 1 1559759211640004,
    decodeIntegerRow 32 3 1 323825874056852,
    decodeIntegerRow 32 3 1 1067249469390436,
    decodeIntegerRow 32 3 1 1202822705487076,
    decodeIntegerRow 32 3 1 278658323978772,
    decodeIntegerRow 32 3 1 1513420102081596,
    decodeIntegerRow 32 3 1 792730340786572,
    decodeIntegerRow 32 3 1 339642948471044,
    decodeIntegerRow 32 3 1 792546647483212,
    decodeIntegerRow 32 3 1 1202629656722596,
    decodeIntegerRow 32 3 1 1574445037357868,
    decodeIntegerRow 32 3 1 1060289817965332,
    decodeIntegerRow 32 3 1 339600073932444,
    decodeIntegerRow 32 3 1 278658317763212,
    decodeIntegerRow 32 3 1 1202822678218564,
    decodeIntegerRow 32 3 1 278575157718068,
    decodeIntegerRow 32 3 1 650390504862724,
    decodeIntegerRow 32 3 1 792546617379412,
    decodeIntegerRow 32 3 1 339642961299876]

def cols_right0 (r : LeftIndex 5 2 3) : List ℤ := cols_right0Data.getD (leftPosition 5 2 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 2 3) : (tripleIndices 2 4 4).map (fun j => (right0Middle5 2 3) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_1_2
  · exact cols_right0_eq_0_1_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_1_2
  · exact cols_right0_eq_1_1_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_1_2
  · exact cols_right0_eq_2_1_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_1_2
  · exact cols_right0_eq_3_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 17 8 1187811545957087630265683827674338723600,
    decodeIntegerRow 32 17 8 1183728988640418681316298330414022326784,
    decodeIntegerRow 32 17 8 2298267136091041738613318051951954139648,
    decodeIntegerRow 32 17 8 1118408071573715498469616479452240034800,
    decodeIntegerRow 32 17 8 1183955800095822993438948369680557357056,
    decodeIntegerRow 32 17 8 1183955843545252921709272454352206013200,
    decodeIntegerRow 32 17 8 1183956582185561702304776684497800466960,
    decodeIntegerRow 32 17 8 1183969139070810972428353255997591935488,
    decodeIntegerRow 32 17 8 1118408071573715498469625801408035710976,
    decodeIntegerRow 32 17 8 2298267136091041738613476525200480634640,
    decodeIntegerRow 32 17 8 1184182606120048564530502012131879335440,
    decodeIntegerRow 32 17 8 1180100048803379615624221238470769576448,
    decodeIntegerRow 32 17 8 1183969139070810972428353257894997959440,
    decodeIntegerRow 32 17 8 1183956582185561702304776684386188347904,
    decodeIntegerRow 32 17 8 1183955751215214324134834391319086156288,
    decodeIntegerRow 32 17 8 1183955794664644252405157895384491483120,
    decodeIntegerRow 32 17 8 1183955797370837119909883960988682454000,
    decodeIntegerRow 32 17 8 1183955797539974174128929339080936790528,
    decodeIntegerRow 32 17 8 1183955797380266136773306329240461735936,
    decodeIntegerRow 32 17 8 1183955797379680887450749078794146296560,
    decodeIntegerRow 32 17 8 1183955797380231710342567667449876846592,
    decodeIntegerRow 32 17 8 1183955797380233510417377532118675695600,
    decodeIntegerRow 32 17 8 1183955797380233629539975243751169776400,
    decodeIntegerRow 32 17 8 1183955797380233623311342683665810569216,
    decodeIntegerRow 32 17 8 1183955797380786358393357218520239532032,
    decodeIntegerRow 32 17 8 1183955797380201109070799968080103310320,
    decodeIntegerRow 32 17 8 1183955797539974174128929339080959508240,
    decodeIntegerRow 32 17 8 1183955797370837119909883960988683790336,
    decodeIntegerRow 32 17 8 1183955797380233622532763613655140673520,
    decodeIntegerRow 32 17 8 1183955797380233616304131053569781549568,
    decodeIntegerRow 32 17 8 1183955797380233510417377532118675695616,
    decodeIntegerRow 32 17 8 1183955797380231710342567667449876846320]

def cols_left0 (r : LeftIndex 5 2 3) : List ℤ := cols_left0Data.getD (leftPosition 5 2 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 2 3) : (tripleIndices 2 4 4).map (fun j => (left0Middle5 2 3) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_1_2
  · exact cols_left0_eq_0_1_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_1_2
  · exact cols_left0_eq_1_1_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_1_2
  · exact cols_left0_eq_2_1_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_1_2
  · exact cols_left0_eq_3_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 10154988518082251602560,
    decodeIntegerRow 32 5 2 20865255441961082982752,
    decodeIntegerRow 32 5 2 21044069681487442420272,
    decodeIntegerRow 32 5 2 9403968101944555040064,
    decodeIntegerRow 32 5 2 2387815484685645532752,
    decodeIntegerRow 32 5 2 10147843590224829728064,
    decodeIntegerRow 32 5 2 13874316447891626600064,
    decodeIntegerRow 32 5 2 21014457712464004920352,
    decodeIntegerRow 32 5 2 9403968101821314100560,
    decodeIntegerRow 32 5 2 21044069681458114220352,
    decodeIntegerRow 32 5 2 2417808923406395482752,
    decodeIntegerRow 32 5 2 13128075847183814102560,
    decodeIntegerRow 32 5 2 2268606652893692420352,
    decodeIntegerRow 32 5 2 9408747917618189100064,
    decodeIntegerRow 32 5 2 10147843590103539412560,
    decodeIntegerRow 32 5 2 2387815484705223607872,
    decodeIntegerRow 32 5 2 21014505853362411170352,
    decodeIntegerRow 32 5 2 13874327904067601600064,
    decodeIntegerRow 32 5 2 13135228386367408162560,
    decodeIntegerRow 32 5 2 20895296106023536107872,
    decodeIntegerRow 32 5 2 9403979533706080040064,
    decodeIntegerRow 32 5 2 21044021691956161170272,
    decodeIntegerRow 32 5 2 2417856302556786157872,
    decodeIntegerRow 32 5 2 13128068199478736288064,
    decodeIntegerRow 32 5 2 20895296106043114282752,
    decodeIntegerRow 32 5 2 13135228386246117228064,
    decodeIntegerRow 32 5 2 9408736461196507850064,
    decodeIntegerRow 32 5 2 2268558512053817420352,
    decodeIntegerRow 32 5 2 10154996165787330038064,
    decodeIntegerRow 32 5 2 20865208062810692407872,
    decodeIntegerRow 32 5 2 21044021691985489220352,
    decodeIntegerRow 32 5 2 9403979533829320350560]

def cols_right2 (r : LeftIndex 5 2 3) : List ℤ := cols_right2Data.getD (leftPosition 5 2 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 2 3) : (tripleIndices 8 1 4).map (fun j => (right2Middle5 2 3) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_1_2
  · exact cols_right2_eq_0_1_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_1_2
  · exact cols_right2_eq_1_1_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_1_2
  · exact cols_right2_eq_2_1_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_1_2
  · exact cols_right2_eq_3_1_3

theorem product0_eq : HexagonAtoms523.outerABC * HexagonAtoms523.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms523.assocBAC * HexagonAtoms523.innerABC = HexagonAtoms523.assocBAC :=
  Matrix.mul_one (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms523.innerRightABC * HexagonAtoms523.assocABC = HexagonAtoms523.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms523.inverseACB * right0Middle5 2 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms523.innerACB * right1Middle5 2 3 = right1Middle5 2 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms523.assocBCA * left0Middle5 2 3 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms523.innerRightBAC * left1Middle5 2 3 = left1Middle5 2 3 :=
  Matrix.one_mul (m := Fin 8 × Fin 1 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms523.assocCAB * right2Middle5 2 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn523
