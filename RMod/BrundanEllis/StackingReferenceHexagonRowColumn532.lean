import RMod.BrundanEllis.StackingReferenceHexagonAtoms532
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn532
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

def rows_outerABC (r : LeftIndex 3 2 5) : List ℤ := rows_outerABCData.getD (leftPosition 3 2 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 2 5) : (tripleIndices 2 4 4).map ((HexagonAtoms532.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 293345176593956,
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

def rows_inverseACB (r : LeftIndex 5 2 3) : List ℤ := rows_inverseACBData.getD (leftPosition 5 2 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 2 3) : (tripleIndices 2 4 4).map ((HexagonAtoms532.inverseACB) r) = rows_inverseACB r := by
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
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 995140486139710,
    decodeIntegerRow 32 3 1 903633306753928,
    decodeIntegerRow 32 3 1 1544183489115544,
    decodeIntegerRow 32 3 1 720618961799830,
    decodeIntegerRow 32 3 1 926792523903352,
    decodeIntegerRow 32 3 1 927357383212510,
    decodeIntegerRow 32 3 1 929051960260810,
    decodeIntegerRow 32 3 1 934135691891224,
    decodeIntegerRow 32 3 1 720618962862712,
    decodeIntegerRow 32 3 1 1544183492304190,
    decodeIntegerRow 32 3 1 949386891663850,
    decodeIntegerRow 32 3 1 857879731409944,
    decodeIntegerRow 32 3 1 934135691930590,
    decodeIntegerRow 32 3 1 929051960247688,
    decodeIntegerRow 32 3 1 925662805993624,
    decodeIntegerRow 32 3 1 926227664830390,
    decodeIntegerRow 32 3 1 926541475485610,
    decodeIntegerRow 32 3 1 926415951247336,
    decodeIntegerRow 32 3 1 926506607642248,
    decodeIntegerRow 32 3 1 926520554781310,
    decodeIntegerRow 32 3 1 926511256687384,
    decodeIntegerRow 32 3 1 926510481846410,
    decodeIntegerRow 32 3 1 926509965285730,
    decodeIntegerRow 32 3 1 926510051379208,
    decodeIntegerRow 32 3 1 926499634074904,
    decodeIntegerRow 32 3 1 926513581211050,
    decodeIntegerRow 32 3 1 926415951246850,
    decodeIntegerRow 32 3 1 926541475485448,
    decodeIntegerRow 32 3 1 926510137472650,
    decodeIntegerRow 32 3 1 926510223566056,
    decodeIntegerRow 32 3 1 926510481846408,
    decodeIntegerRow 32 3 1 926511256687390]

def rows_assocBCA (r : RightIndex 3 2 5) : List ℤ := rows_assocBCAData.getD (rightPosition 3 2 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 2 5) : (tripleIndices 2 4 4).map ((HexagonAtoms532.assocBCA) r) = rows_assocBCA r := by
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
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_1_0
  · exact rows_assocBCA_eq_2_1_1
  · exact rows_assocBCA_eq_2_1_2
  · exact rows_assocBCA_eq_2_1_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_1_0
  · exact rows_assocBCA_eq_3_1_1
  · exact rows_assocBCA_eq_3_1_2
  · exact rows_assocBCA_eq_3_1_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 1517820175505588,
    decodeIntegerRow 32 3 1 1071635901813124,
    decodeIntegerRow 32 3 1 644623276160212,
    decodeIntegerRow 32 3 1 287564349620516,
    decodeIntegerRow 32 3 1 1568846039545956,
    decodeIntegerRow 32 3 1 1193708136413332,
    decodeIntegerRow 32 3 1 1055822113830076,
    decodeIntegerRow 32 3 1 1524597961445132,
    decodeIntegerRow 32 3 1 1524597967453116,
    decodeIntegerRow 32 3 1 1055822086042228,
    decodeIntegerRow 32 3 1 659312022594844,
    decodeIntegerRow 32 3 1 284174161720212,
    decodeIntegerRow 32 3 1 287564336523732,
    decodeIntegerRow 32 3 1 644623305846364,
    decodeIntegerRow 32 3 1 781384259565772,
    decodeIntegerRow 32 3 1 335200020088964,
    decodeIntegerRow 32 3 1 1193668735456324,
    decodeIntegerRow 32 3 1 284356507629452,
    decodeIntegerRow 32 3 1 1524793743942116,
    decodeIntegerRow 32 3 1 797116658418028,
    decodeIntegerRow 32 3 1 1071721850545708,
    decodeIntegerRow 32 3 1 335005276725156,
    decodeIntegerRow 32 3 1 287744616192308,
    decodeIntegerRow 32 3 1 1208352630980476,
    decodeIntegerRow 32 3 1 1208352660658252,
    decodeIntegerRow 32 3 1 287744629287036,
    decodeIntegerRow 32 3 1 1518014918873388,
    decodeIntegerRow 32 3 1 781298365788124,
    decodeIntegerRow 32 3 1 797116630621084,
    decodeIntegerRow 32 3 1 1524793737930348,
    decodeIntegerRow 32 3 1 1568663693634884,
    decodeIntegerRow 32 3 1 659351483230708]

def rows_assocCAB (r : RightIndex 2 5 3) : List ℤ := rows_assocCABData.getD (rightPosition 2 5 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_4_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_5_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_6_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_7_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 5 3) : (tripleIndices 4 2 4).map ((HexagonAtoms532.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_4_0_0
  · exact rows_assocCAB_eq_4_0_1
  · exact rows_assocCAB_eq_4_0_2
  · exact rows_assocCAB_eq_4_0_3
  · exact rows_assocCAB_eq_5_0_0
  · exact rows_assocCAB_eq_5_0_1
  · exact rows_assocCAB_eq_5_0_2
  · exact rows_assocCAB_eq_5_0_3
  · exact rows_assocCAB_eq_6_0_0
  · exact rows_assocCAB_eq_6_0_1
  · exact rows_assocCAB_eq_6_0_2
  · exact rows_assocCAB_eq_6_0_3
  · exact rows_assocCAB_eq_7_0_0
  · exact rows_assocCAB_eq_7_0_1
  · exact rows_assocCAB_eq_7_0_2
  · exact rows_assocCAB_eq_7_0_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926802984258742,
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

def cols_assocABC (r : LeftIndex 5 3 2) : List ℤ := cols_assocABCData.getD (leftPosition 5 3 2 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 3 2) : (tripleIndices 2 4 4).map (fun j => (HexagonAtoms532.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_4_0_0
  · exact cols_assocABC_eq_4_0_1
  · exact cols_assocABC_eq_4_0_2
  · exact cols_assocABC_eq_4_0_3
  · exact cols_assocABC_eq_5_0_0
  · exact cols_assocABC_eq_5_0_1
  · exact cols_assocABC_eq_5_0_2
  · exact cols_assocABC_eq_5_0_3
  · exact cols_assocABC_eq_6_0_0
  · exact cols_assocABC_eq_6_0_1
  · exact cols_assocABC_eq_6_0_2
  · exact cols_assocABC_eq_6_0_3
  · exact cols_assocABC_eq_7_0_0
  · exact cols_assocABC_eq_7_0_1
  · exact cols_assocABC_eq_7_0_2
  · exact cols_assocABC_eq_7_0_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 926802984258742,
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

def cols_right0 (r : LeftIndex 5 3 2) : List ℤ := cols_right0Data.getD (leftPosition 5 3 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 3 2) : (tripleIndices 2 4 4).map (fun j => (right0Middle5 3 2) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_0_2
  · exact cols_right0_eq_0_0_3
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_0_2
  · exact cols_right0_eq_1_0_3
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_4_0_0
  · exact cols_right0_eq_4_0_1
  · exact cols_right0_eq_4_0_2
  · exact cols_right0_eq_4_0_3
  · exact cols_right0_eq_5_0_0
  · exact cols_right0_eq_5_0_1
  · exact cols_right0_eq_5_0_2
  · exact cols_right0_eq_5_0_3
  · exact cols_right0_eq_6_0_0
  · exact cols_right0_eq_6_0_1
  · exact cols_right0_eq_6_0_2
  · exact cols_right0_eq_6_0_3
  · exact cols_right0_eq_7_0_0
  · exact cols_right0_eq_7_0_1
  · exact cols_right0_eq_7_0_2
  · exact cols_right0_eq_7_0_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11645132112441528320272,
    decodeIntegerRow 32 5 2 11626515626892700195560,
    decodeIntegerRow 32 5 2 11656308412542114258064,
    decodeIntegerRow 32 5 2 11639123964249145507752,
    decodeIntegerRow 32 5 2 11639123964370239257872,
    decodeIntegerRow 32 5 2 11656308412561645507560,
    decodeIntegerRow 32 5 2 11656548738464965820560,
    decodeIntegerRow 32 5 2 11637932252822387695272,
    decodeIntegerRow 32 5 2 11645084810318481445272,
    decodeIntegerRow 32 5 2 11626507997527465820560,
    decodeIntegerRow 32 5 2 11656319856653442383064,
    decodeIntegerRow 32 5 2 11639172029555786132752,
    decodeIntegerRow 32 5 2 11643892335952270507752,
    decodeIntegerRow 32 5 2 11626744508753051758064,
    decodeIntegerRow 32 5 2 11626507997498168945064,
    decodeIntegerRow 32 5 2 11645084810195434570352,
    decodeIntegerRow 32 5 2 20880252132034317540312,
    decodeIntegerRow 32 5 2 13131648263626001795312,
    decodeIntegerRow 32 5 2 9406358041458031470312,
    decodeIntegerRow 32 5 2 2253800624465965975312,
    decodeIntegerRow 32 5 2 21029263740921044100312,
    decodeIntegerRow 32 5 2 13876706323928734595312,
    decodeIntegerRow 32 5 2 13131648263626195470312,
    decodeIntegerRow 32 5 2 20880252132034285975312,
    decodeIntegerRow 32 5 2 2402812251663223475312,
    decodeIntegerRow 32 5 2 10151416024856470470312,
    decodeIntegerRow 32 5 2 13876706399612328295312,
    decodeIntegerRow 32 5 2 21029263728714012540312,
    decodeIntegerRow 32 5 2 21029263728713965975312,
    decodeIntegerRow 32 5 2 13876706399612525220312,
    decodeIntegerRow 32 5 2 13131648340530298595312,
    decodeIntegerRow 32 5 2 20880252113723770350312]

def cols_left0 (r : LeftIndex 5 3 2) : List ℤ := cols_left0Data.getD (leftPosition 5 3 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_4_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_5_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_6_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_0 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_1 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_2 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_7_0_3 : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 3 2) : (tripleIndices 2 4 4).map (fun j => (left0Middle5 3 2) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_0_2
  · exact cols_left0_eq_0_0_3
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_0_2
  · exact cols_left0_eq_1_0_3
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_4_0_0
  · exact cols_left0_eq_4_0_1
  · exact cols_left0_eq_4_0_2
  · exact cols_left0_eq_4_0_3
  · exact cols_left0_eq_5_0_0
  · exact cols_left0_eq_5_0_1
  · exact cols_left0_eq_5_0_2
  · exact cols_left0_eq_5_0_3
  · exact cols_left0_eq_6_0_0
  · exact cols_left0_eq_6_0_1
  · exact cols_left0_eq_6_0_2
  · exact cols_left0_eq_6_0_3
  · exact cols_left0_eq_7_0_0
  · exact cols_left0_eq_7_0_1
  · exact cols_left0_eq_7_0_2
  · exact cols_left0_eq_7_0_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 2406412547673851795560,
    decodeIntegerRow 32 5 2 10136401452773535975352,
    decodeIntegerRow 32 5 2 13891492166885848787752,
    decodeIntegerRow 32 5 2 21026903190979517357560,
    decodeIntegerRow 32 5 2 2251392784485570483064,
    decodeIntegerRow 32 5 2 9421136179337051912872,
    decodeIntegerRow 32 5 2 10166442117935645665352,
    decodeIntegerRow 32 5 2 2399260002527367345560,
    decodeIntegerRow 32 5 2 2399260002508033045064,
    decodeIntegerRow 32 5 2 10166442118056785975272,
    decodeIntegerRow 32 5 2 13861928186172989412872,
    decodeIntegerRow 32 5 2 21031671580872289233064,
    decodeIntegerRow 32 5 2 21026903191009008033064,
    decodeIntegerRow 32 5 2 13891492166762832852872,
    decodeIntegerRow 32 5 2 13146662912734473475352,
    decodeIntegerRow 32 5 2 20876651817693383045560,
    decodeIntegerRow 32 5 2 9421143731704208162872,
    decodeIntegerRow 32 5 2 21031624260315648657560,
    decodeIntegerRow 32 5 2 2399211925115454845560,
    decodeIntegerRow 32 5 2 13116633615738379725272,
    decodeIntegerRow 32 5 2 10136389932877098475352,
    decodeIntegerRow 32 5 2 20876699870671898595064,
    decodeIntegerRow 32 5 2 21026855907073461107560,
    decodeIntegerRow 32 5 2 9391579904922957852872,
    decodeIntegerRow 32 5 2 9391579904799942537752,
    decodeIntegerRow 32 5 2 21026855907043970533064,
    decodeIntegerRow 32 5 2 2406364494695336095064,
    decodeIntegerRow 32 5 2 13146674432388817225352,
    decodeIntegerRow 32 5 2 13116633615859520665352,
    decodeIntegerRow 32 5 2 2399211925134789295064,
    decodeIntegerRow 32 5 2 2251440105042211157560,
    decodeIntegerRow 32 5 2 13861920633559676912872]

def cols_right2 (r : LeftIndex 5 3 2) : List ℤ := cols_right2Data.getD (leftPosition 5 3 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_4_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_5_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_6_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_7_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 3 2) : (tripleIndices 4 2 4).map (fun j => (right2Middle5 3 2) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_0_2
  · exact cols_right2_eq_0_0_3
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_0_2
  · exact cols_right2_eq_1_0_3
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_4_0_0
  · exact cols_right2_eq_4_0_1
  · exact cols_right2_eq_4_0_2
  · exact cols_right2_eq_4_0_3
  · exact cols_right2_eq_5_0_0
  · exact cols_right2_eq_5_0_1
  · exact cols_right2_eq_5_0_2
  · exact cols_right2_eq_5_0_3
  · exact cols_right2_eq_6_0_0
  · exact cols_right2_eq_6_0_1
  · exact cols_right2_eq_6_0_2
  · exact cols_right2_eq_6_0_3
  · exact cols_right2_eq_7_0_0
  · exact cols_right2_eq_7_0_1
  · exact cols_right2_eq_7_0_2
  · exact cols_right2_eq_7_0_3

theorem product0_eq : HexagonAtoms532.outerABC * HexagonAtoms532.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms532.assocBAC * HexagonAtoms532.innerABC = HexagonAtoms532.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms532.innerRightABC * HexagonAtoms532.assocABC = HexagonAtoms532.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms532.inverseACB * right0Middle5 3 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms532.innerACB * right1Middle5 3 2 = right1Middle5 3 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms532.assocBCA * left0Middle5 3 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms532.innerRightBAC * left1Middle5 3 2 = left1Middle5 3 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 8 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms532.assocCAB * right2Middle5 3 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn532
