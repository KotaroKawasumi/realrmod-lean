import RMod.BrundanEllis.StackingReferenceHexagonAtoms332
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn332
open Superfusion

theorem assocBAC_alias : HexagonAtoms332.assocBAC = HexagonAtoms332.assocABC :=
  HexagonAtoms332.assocBAC_eq.symm.trans HexagonAtoms332.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms332.innerRightBAC = HexagonAtoms332.innerRightABC :=
  HexagonAtoms332.innerRightBAC_eq.symm.trans HexagonAtoms332.innerRightABC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def rows_outerABC (r : LeftIndex 3 2 3) : List ℤ := rows_outerABCData.getD (leftPosition 3 2 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_outerABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 2 3) : (tripleIndices 2 8 1).map ((HexagonAtoms332.outerABC) r) = rows_outerABC r := by
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

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 20998480,
    decodeIntegerRow 16 3 1 19948720,
    decodeIntegerRow 16 3 1 21524098,
    decodeIntegerRow 16 3 1 21521146,
    decodeIntegerRow 16 3 1 6997306,
    decodeIntegerRow 16 3 1 16681342,
    decodeIntegerRow 16 3 1 21523600,
    decodeIntegerRow 16 3 1 21523280,
    decodeIntegerRow 16 3 1 21523114,
    decodeIntegerRow 16 3 1 21523442,
    decodeIntegerRow 16 3 1 35695120,
    decodeIntegerRow 16 3 1 26247280,
    decodeIntegerRow 16 3 1 21524080,
    decodeIntegerRow 16 3 1 21521200,
    decodeIntegerRow 16 3 1 20985358,
    decodeIntegerRow 16 3 1 19909354]

def rows_assocABC (r : RightIndex 3 3 2) : List ℤ := rows_assocABCData.getD (rightPosition 3 3 2 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocABC ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_4_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_5_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_6_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_7_0 : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocABC ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 3 3 2) : (tripleIndices 4 4 1).map ((HexagonAtoms332.assocABC) r) = rows_assocABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 21497116,
    decodeIntegerRow 16 3 1 21510238,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 2391484,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523342,
    decodeIntegerRow 16 3 1 21523396,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21523684,
    decodeIntegerRow 16 3 1 21523522]

def rows_inverseACB (r : LeftIndex 3 2 3) : List ℤ := rows_inverseACBData.getD (leftPosition 3 2 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_inverseACB ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 2 3) : (tripleIndices 2 8 1).map ((HexagonAtoms332.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 21549604,
    decodeIntegerRow 16 3 1 21536482,
    decodeIntegerRow 16 3 1 11957422,
    decodeIntegerRow 16 3 1 40655236,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523378,
    decodeIntegerRow 16 3 1 21523324,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21523036,
    decodeIntegerRow 16 3 1 21523198]

def rows_assocBCA (r : RightIndex 3 2 3) : List ℤ := rows_assocBCAData.getD (rightPosition 3 2 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((0 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_4_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (4 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_5_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (5 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_6_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (6 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_7_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1))) = rows_assocBCA ((1 : Fin 2), (7 : Fin 8), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 2 3) : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523328,
    decodeIntegerRow 16 3 1 21523344,
    decodeIntegerRow 16 3 1 21785800,
    decodeIntegerRow 16 3 1 21392140,
    decodeIntegerRow 16 3 1 21523320,
    decodeIntegerRow 16 3 1 21523340,
    decodeIntegerRow 16 3 1 21313408,
    decodeIntegerRow 16 3 1 21628336,
    decodeIntegerRow 16 3 1 21526600,
    decodeIntegerRow 16 3 1 21524980,
    decodeIntegerRow 16 3 1 4517248,
    decodeIntegerRow 16 3 1 30026416,
    decodeIntegerRow 16 3 1 21520768,
    decodeIntegerRow 16 3 1 21522064,
    decodeIntegerRow 16 3 1 265720,
    decodeIntegerRow 16 3 1 32152180]

def rows_assocCAB (r : RightIndex 2 3 3) : List ℤ := rows_assocCABData.getD (rightPosition 2 3 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_2_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_3_0 : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = rows_assocCAB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 3 3) : (tripleIndices 2 8 1).map ((HexagonAtoms332.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21700264,
    decodeIntegerRow 16 3 1 21582328]

def cols_assocABC (r : LeftIndex 3 3 2) : List ℤ := cols_assocABCData.getD (leftPosition 3 3 2 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 3 2) : (tripleIndices 2 8 1).map (fun j => (HexagonAtoms332.assocABC) j r) = cols_assocABC r := by
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

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 23621404,
    decodeIntegerRow 16 3 1 22570168,
    decodeIntegerRow 16 3 1 40418876,
    decodeIntegerRow 16 3 1 30970872,
    decodeIntegerRow 16 3 1 19422364,
    decodeIntegerRow 16 3 1 20470648,
    decodeIntegerRow 16 3 1 2627516,
    decodeIntegerRow 16 3 1 12075192,
    decodeIntegerRow 16 3 1 40891272,
    decodeIntegerRow 16 3 1 11839644,
    decodeIntegerRow 16 3 1 23673928,
    decodeIntegerRow 16 3 1 20450236,
    decodeIntegerRow 16 3 1 40891592,
    decodeIntegerRow 16 3 1 11839004,
    decodeIntegerRow 16 3 1 23676808,
    decodeIntegerRow 16 3 1 20444476]

def cols_innerABC (r : LeftIndex 3 3 2) : List ℤ := cols_innerABCData.getD (leftPosition 3 3 2 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_2_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_3_0 : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 3 3 2) : (tripleIndices 4 4 1).map (fun j => (HexagonAtoms332.innerABC) j r) = cols_innerABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21700264,
    decodeIntegerRow 16 3 1 21582328]

def cols_right0 (r : LeftIndex 3 3 2) : List ℤ := cols_right0Data.getD (leftPosition 3 3 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 3 2) : (tripleIndices 2 8 1).map (fun j => (right0Middle3 3 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 20991910,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 22054792,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21700750,
    decodeIntegerRow 16 3 1 21582490]

def cols_left0 (r : LeftIndex 3 3 2) : List ℤ := cols_left0Data.getD (leftPosition 3 3 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_left0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 3 2) : (tripleIndices 2 8 1).map (fun j => (left0Middle3 3 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523328,
    decodeIntegerRow 16 3 1 21523344,
    decodeIntegerRow 16 3 1 21785800,
    decodeIntegerRow 16 3 1 21392140,
    decodeIntegerRow 16 3 1 21523320,
    decodeIntegerRow 16 3 1 21523340,
    decodeIntegerRow 16 3 1 21313408,
    decodeIntegerRow 16 3 1 21628336,
    decodeIntegerRow 16 3 1 21526600,
    decodeIntegerRow 16 3 1 21524980,
    decodeIntegerRow 16 3 1 4517248,
    decodeIntegerRow 16 3 1 30026416,
    decodeIntegerRow 16 3 1 21520768,
    decodeIntegerRow 16 3 1 21522064,
    decodeIntegerRow 16 3 1 265720,
    decodeIntegerRow 16 3 1 32152180]

def cols_right2 (r : LeftIndex 3 3 2) : List ℤ := cols_right2Data.getD (leftPosition 3 3 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_2_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_3_0 : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1))) = cols_right2 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 1)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 3 2) : (tripleIndices 2 8 1).map (fun j => (right2Middle3 3 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms332.outerABC * HexagonAtoms332.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms332.assocABC * HexagonAtoms332.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms332.innerRightABC * HexagonAtoms332.assocABC = HexagonAtoms332.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 4 × Fin 4 × Fin 1) _

theorem product3_eq : HexagonAtoms332.inverseACB * right0Middle3 3 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms332.innerACB * right1Middle3 3 2 = right1Middle3 3 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 4 × Fin 4 × Fin 1) _

theorem product5_eq : HexagonAtoms332.assocBCA * left0Middle3 3 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms332.innerRightABC * left1Middle3 3 2 = left1Middle3 3 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 8 × Fin 1) (n := Fin 4 × Fin 4 × Fin 1) _

theorem product7_eq : HexagonAtoms332.assocCAB * right2Middle3 3 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn332
