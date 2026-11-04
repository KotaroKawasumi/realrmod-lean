import RMod.BrundanEllis.StackingReferenceHexagonAtoms330
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn330
open Superfusion

theorem assocBAC_alias : HexagonAtoms330.assocBAC = HexagonAtoms330.assocABC :=
  HexagonAtoms330.assocBAC_eq.symm.trans HexagonAtoms330.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms330.innerRightBAC = HexagonAtoms330.innerRightABC :=
  HexagonAtoms330.innerRightBAC_eq.symm.trans HexagonAtoms330.innerRightABC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
    decodeIntegerRow 16 3 1 27824216,
    decodeIntegerRow 16 3 1 24674772,
    decodeIntegerRow 16 3 1 36220984,
    decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 27981624,
    decodeIntegerRow 16 3 1 7534828,
    decodeIntegerRow 16 3 1 36588376,
    decodeIntegerRow 16 3 1 24753452,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 36586456,
    decodeIntegerRow 16 3 1 24749292]

def rows_outerABC (r : LeftIndex 3 0 3) : List ℤ := rows_outerABCData.getD (leftPosition 3 0 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_2_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_3_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_outerABC ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 0 3) : (tripleIndices 1 4 4).map ((HexagonAtoms330.outerABC) r) = rows_outerABC r := by
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

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def rows_assocABC (r : RightIndex 3 3 0) : List ℤ := rows_assocABCData.getD (rightPosition 3 3 0 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocABC ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocABC ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocABC ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocABC ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocABC ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocABC ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocABC ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocABC ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocABC ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_1 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocABC ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_2 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocABC ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_3 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocABC ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocABC ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_1 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocABC ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_2 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocABC ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_3 : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocABC ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 3 3 0) : (tripleIndices 4 1 4).map ((HexagonAtoms330.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_0_1_2
  · exact rows_assocABC_eq_0_1_3
  · exact rows_assocABC_eq_0_2_0
  · exact rows_assocABC_eq_0_2_1
  · exact rows_assocABC_eq_0_2_2
  · exact rows_assocABC_eq_0_2_3
  · exact rows_assocABC_eq_0_3_0
  · exact rows_assocABC_eq_0_3_1
  · exact rows_assocABC_eq_0_3_2
  · exact rows_assocABC_eq_0_3_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def rows_assocCAB (r : RightIndex 0 3 3) : List ℤ := rows_assocCABData.getD (rightPosition 0 3 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 0 3 3) : (tripleIndices 1 4 4).map ((HexagonAtoms330.assocCAB) r) = rows_assocCAB r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def cols_assocABC (r : LeftIndex 3 3 0) : List ℤ := cols_assocABCData.getD (leftPosition 3 3 0 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 3 0) : (tripleIndices 1 4 4).map (fun j => (HexagonAtoms330.assocABC) j r) = cols_assocABC r := by
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

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
    decodeIntegerRow 16 3 1 27824216,
    decodeIntegerRow 16 3 1 24674772,
    decodeIntegerRow 16 3 1 36220984,
    decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 27981624,
    decodeIntegerRow 16 3 1 7534828,
    decodeIntegerRow 16 3 1 36588376,
    decodeIntegerRow 16 3 1 24753452,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 36586456,
    decodeIntegerRow 16 3 1 24749292]

def cols_innerABC (r : LeftIndex 3 3 0) : List ℤ := cols_innerABCData.getD (leftPosition 3 3 0 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 3 3 0) : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms330.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_0_2
  · exact cols_innerABC_eq_1_0_3
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_0_2
  · exact cols_innerABC_eq_2_0_3
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_0_2
  · exact cols_innerABC_eq_3_0_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def cols_right2 (r : LeftIndex 3 3 0) : List ℤ := cols_right2Data.getD (leftPosition 3 3 0 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 3 0) : (tripleIndices 1 4 4).map (fun j => (right2Middle3 3 0) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms330.outerABC * HexagonAtoms330.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms330.assocABC * HexagonAtoms330.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms330.innerRightABC * HexagonAtoms330.assocABC = HexagonAtoms330.assocABC :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms330.inverseACB * right0Middle3 3 0 = right0Middle3 3 0 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product4_eq : HexagonAtoms330.innerACB * right1Middle3 3 0 = right1Middle3 3 0 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms330.assocBCA * left0Middle3 3 0 = left0Middle3 3 0 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product6_eq : HexagonAtoms330.innerRightABC * left1Middle3 3 0 = left1Middle3 3 0 :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms330.assocCAB * right2Middle3 3 0 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn330
