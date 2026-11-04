import RMod.BrundanEllis.StackingReferenceHexagonAtoms541
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn541
open Superfusion

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 36575260,
    decodeIntegerRow 16 3 1 27937776,
    decodeIntegerRow 16 3 1 24635408,
    decodeIntegerRow 16 3 1 35156620,
    decodeIntegerRow 16 3 1 35157616,
    decodeIntegerRow 16 3 1 24631140,
    decodeIntegerRow 16 3 1 15104460,
    decodeIntegerRow 16 3 1 6473392,
    decodeIntegerRow 16 3 1 18253904,
    decodeIntegerRow 16 3 1 35524060,
    decodeIntegerRow 16 3 1 36234100,
    decodeIntegerRow 16 3 1 15187728,
    decodeIntegerRow 16 3 1 27863580,
    decodeIntegerRow 16 3 1 6814576,
    decodeIntegerRow 16 3 1 35525008,
    decodeIntegerRow 16 3 1 18258060]

def rows_outerABC (r : LeftIndex 4 1 5) : List ℤ := rows_outerABCData.getD (leftPosition 4 1 5 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 4 1 5) : (tripleIndices 1 4 4).map ((HexagonAtoms541.outerABC) r) = rows_outerABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21560458,
    decodeIntegerRow 16 3 1 21351802,
    decodeIntegerRow 16 3 1 21339166,
    decodeIntegerRow 16 3 1 21599986,
    decodeIntegerRow 16 3 1 21353746,
    decodeIntegerRow 16 3 1 21481726,
    decodeIntegerRow 16 3 1 21604198,
    decodeIntegerRow 16 3 1 21706582,
    decodeIntegerRow 16 3 1 7705882,
    decodeIntegerRow 16 3 1 18334742,
    decodeIntegerRow 16 3 1 27900626,
    decodeIntegerRow 16 3 1 36403714,
    decodeIntegerRow 16 3 1 18334686,
    decodeIntegerRow 16 3 1 35340814,
    decodeIntegerRow 16 3 1 36403702,
    decodeIntegerRow 16 3 1 15146042]

def rows_inverseACB (r : LeftIndex 5 1 4) : List ℤ := rows_inverseACBData.getD (leftPosition 5 1 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 1 4) : (tripleIndices 1 4 4).map ((HexagonAtoms541.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 20991922,
    decodeIntegerRow 16 3 1 19929036,
    decodeIntegerRow 16 3 1 16740418,
    decodeIntegerRow 16 3 1 7174444,
    decodeIntegerRow 16 3 1 21584596,
    decodeIntegerRow 16 3 1 21346942,
    decodeIntegerRow 16 3 1 21516556,
    decodeIntegerRow 16 3 1 21542962,
    decodeIntegerRow 16 3 1 21503596,
    decodeIntegerRow 16 3 1 21529678,
    decodeIntegerRow 16 3 1 21345484,
    decodeIntegerRow 16 3 1 21580222,
    decodeIntegerRow 16 3 1 35872258,
    decodeIntegerRow 16 3 1 26306356,
    decodeIntegerRow 16 3 1 19929038,
    decodeIntegerRow 16 3 1 20991916]

def rows_assocBCA (r : RightIndex 4 1 5) : List ℤ := rows_assocBCAData.getD (rightPosition 4 1 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 4 1 5) : (tripleIndices 1 4 4).map ((HexagonAtoms541.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21483968,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21707080,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 35340340,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 15148336,
    decodeIntegerRow 16 3 1 6642040,
    decodeIntegerRow 16 3 1 21693952,
    decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21444600,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 15143800]

def rows_assocCAB (r : RightIndex 1 5 4) : List ℤ := rows_assocCABData.getD (rightPosition 1 5 4 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 1 5 4) : (tripleIndices 2 2 4).map ((HexagonAtoms541.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 7521688,
    decodeIntegerRow 16 3 1 18258116,
    decodeIntegerRow 16 3 1 27863528,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 6473404,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 24792872,
    decodeIntegerRow 16 3 1 7522684,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 27859044]

def cols_assocABC (r : LeftIndex 5 4 1) : List ℤ := cols_assocABCData.getD (leftPosition 5 4 1 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 4 1) : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms541.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7521688,
    decodeIntegerRow 16 3 1 18258116,
    decodeIntegerRow 16 3 1 27863528,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 6473404,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 24792872,
    decodeIntegerRow 16 3 1 7522684,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 27859044]

def cols_right0 (r : LeftIndex 5 4 1) : List ℤ := cols_right0Data.getD (leftPosition 5 4 1 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 4 1) : (tripleIndices 1 4 4).map (fun j => (right0Middle5 4 1) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 9 4 835001374900792,
    decodeIntegerRow 16 9 4 1750074794755528,
    decodeIntegerRow 16 9 4 927514286207608,
    decodeIntegerRow 16 9 4 916356559118328,
    decodeIntegerRow 16 9 4 936691524008712,
    decodeIntegerRow 16 9 4 925254854167288,
    decodeIntegerRow 16 9 4 1750074450381112,
    decodeIntegerRow 16 9 4 835004474258872,
    decodeIntegerRow 16 9 4 925254849915832,
    decodeIntegerRow 16 9 4 916328703106872,
    decodeIntegerRow 16 9 4 835004474317192,
    decodeIntegerRow 16 9 4 102945737997688,
    decodeIntegerRow 16 9 4 102945393624568,
    decodeIntegerRow 16 9 4 835001374947448,
    decodeIntegerRow 16 9 4 936663591469752,
    decodeIntegerRow 16 9 4 927514290459208]

def cols_left0 (r : LeftIndex 5 4 1) : List ℤ := cols_left0Data.getD (leftPosition 5 4 1 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 4 1) : (tripleIndices 1 4 4).map (fun j => (left0Middle5 4 1) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 926510266613128,
    decodeIntegerRow 16 9 4 926511644104960,
    decodeIntegerRow 16 9 4 926524041563520,
    decodeIntegerRow 16 9 4 926635618664392,
    decodeIntegerRow 16 9 4 835002924632320,
    decodeIntegerRow 16 9 4 1750074623040712,
    decodeIntegerRow 16 9 4 927639814697608,
    decodeIntegerRow 16 9 4 916342650244480,
    decodeIntegerRow 16 9 4 926524041563528,
    decodeIntegerRow 16 9 4 926384570187520,
    decodeIntegerRow 16 9 4 926509922239360,
    decodeIntegerRow 16 9 4 926511644110792,
    decodeIntegerRow 16 9 4 925380378405760,
    decodeIntegerRow 16 9 4 916342611980728,
    decodeIntegerRow 16 9 4 835002924579832,
    decodeIntegerRow 16 9 4 102945566283520]

def cols_right2 (r : LeftIndex 5 4 1) : List ℤ := cols_right2Data.getD (leftPosition 5 4 1 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 4 1) : (tripleIndices 2 2 4).map (fun j => (right2Middle5 4 1) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms541.outerABC * HexagonAtoms541.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms541.assocBAC * HexagonAtoms541.innerABC = HexagonAtoms541.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms541.innerRightABC * HexagonAtoms541.assocABC = HexagonAtoms541.assocABC :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms541.inverseACB * right0Middle5 4 1 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms541.innerACB * right1Middle5 4 1 = right1Middle5 4 1 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms541.assocBCA * left0Middle5 4 1 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms541.innerRightBAC * left1Middle5 4 1 = left1Middle5 4 1 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms541.assocCAB * right2Middle5 4 1 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn541
