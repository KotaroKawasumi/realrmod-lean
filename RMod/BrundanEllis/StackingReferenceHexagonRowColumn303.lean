import RMod.BrundanEllis.StackingReferenceHexagonAtoms303
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn303
open Superfusion

theorem assocBCA_alias : HexagonAtoms303.assocBCA = HexagonAtoms303.assocBAC :=
  HexagonAtoms303.assocBCA_eq.symm.trans HexagonAtoms303.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def rows_inverseACB (r : LeftIndex 3 3 0) : List ℤ := rows_inverseACBData.getD (leftPosition 3 3 0 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 3 0) : (tripleIndices 1 4 4).map ((HexagonAtoms303.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
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

def rows_innerACB (r : LeftIndex 3 3 0) : List ℤ := rows_innerACBData.getD (leftPosition 3 3 0 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 3 3 0) : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_2_0_0
  · exact rows_innerACB_eq_2_0_1
  · exact rows_innerACB_eq_2_0_2
  · exact rows_innerACB_eq_2_0_3
  · exact rows_innerACB_eq_3_0_0
  · exact rows_innerACB_eq_3_0_1
  · exact rows_innerACB_eq_3_0_2
  · exact rows_innerACB_eq_3_0_3

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def rows_assocBAC (r : RightIndex 0 3 3) : List ℤ := rows_assocBACData.getD (rightPosition 0 3 3 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 0 3 3) : (tripleIndices 1 4 4).map ((HexagonAtoms303.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_0_2
  · exact rows_assocBAC_eq_2_0_3
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_0_2
  · exact rows_assocBAC_eq_3_0_3

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
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

def rows_innerRightBAC (r : RightIndex 0 3 3) : List ℤ := rows_innerRightBACData.getD (rightPosition 0 3 3 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 0 3 3) : (tripleIndices 4 1 4).map ((HexagonAtoms303.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_2_0_0
  · exact rows_innerRightBAC_eq_2_0_1
  · exact rows_innerRightBAC_eq_2_0_2
  · exact rows_innerRightBAC_eq_2_0_3
  · exact rows_innerRightBAC_eq_3_0_0
  · exact rows_innerRightBAC_eq_3_0_1
  · exact rows_innerRightBAC_eq_3_0_2
  · exact rows_innerRightBAC_eq_3_0_3

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

def rows_assocCAB (r : RightIndex 3 3 0) : List ℤ := rows_assocCABData.getD (rightPosition 3 3 0 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 3 3 0) : (tripleIndices 4 1 4).map ((HexagonAtoms303.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def cols_right0 (r : LeftIndex 3 0 3) : List ℤ := cols_right0Data.getD (leftPosition 3 0 3 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 0 3) : (tripleIndices 1 4 4).map (fun j => (right0Middle3 0 3) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def cols_right1 (r : LeftIndex 3 0 3) : List ℤ := cols_right1Data.getD (leftPosition 3 0 3 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 3 0 3) : (tripleIndices 4 1 4).map (fun j => (right1Middle3 0 3) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_1_2
  · exact cols_right1_eq_0_1_3
  · exact cols_right1_eq_0_2_0
  · exact cols_right1_eq_0_2_1
  · exact cols_right1_eq_0_2_2
  · exact cols_right1_eq_0_2_3
  · exact cols_right1_eq_0_3_0
  · exact cols_right1_eq_0_3_1
  · exact cols_right1_eq_0_3_2
  · exact cols_right1_eq_0_3_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
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

def cols_left0 (r : LeftIndex 3 0 3) : List ℤ := cols_left0Data.getD (leftPosition 3 0 3 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 0 3) : (tripleIndices 1 4 4).map (fun j => (left0Middle3 0 3) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def cols_left1 (r : LeftIndex 3 0 3) : List ℤ := cols_left1Data.getD (leftPosition 3 0 3 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 3 0 3) : (tripleIndices 4 1 4).map (fun j => (left1Middle3 0 3) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_1_2
  · exact cols_left1_eq_0_1_3
  · exact cols_left1_eq_0_2_0
  · exact cols_left1_eq_0_2_1
  · exact cols_left1_eq_0_2_2
  · exact cols_left1_eq_0_2_3
  · exact cols_left1_eq_0_3_0
  · exact cols_left1_eq_0_3_1
  · exact cols_left1_eq_0_3_2
  · exact cols_left1_eq_0_3_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7875988,
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

def cols_right2 (r : LeftIndex 3 0 3) : List ℤ := cols_right2Data.getD (leftPosition 3 0 3 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 0 3) : (tripleIndices 4 1 4).map (fun j => (right2Middle3 0 3) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms303.outerABC * HexagonAtoms303.assocABC = HexagonAtoms303.outerABC :=
  Matrix.mul_one (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product1_eq : HexagonAtoms303.assocBAC * HexagonAtoms303.innerABC = HexagonAtoms303.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product2_eq : HexagonAtoms303.innerRightABC * HexagonAtoms303.assocABC = HexagonAtoms303.assocABC :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms303.inverseACB * right0Middle3 0 3 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms303.innerACB * right1Middle3 0 3 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms303.assocBAC * left0Middle3 0 3 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms303.innerRightBAC * left1Middle3 0 3 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms303.assocCAB * right2Middle3 0 3 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn303
