import RMod.BrundanEllis.StackingReferenceHexagonAtoms505
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn505
open Superfusion

theorem assocBCA_alias : HexagonAtoms505.assocBCA = HexagonAtoms505.assocBAC :=
  HexagonAtoms505.assocBCA_eq.symm.trans HexagonAtoms505.assocBAC_eq

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

def rows_inverseACB (r : LeftIndex 5 5 0) : List ℤ := rows_inverseACBData.getD (leftPosition 5 5 0 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 5 0) : (tripleIndices 1 4 4).map ((HexagonAtoms505.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 36575260,
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

def rows_innerACB (r : LeftIndex 5 5 0) : List ℤ := rows_innerACBData.getD (leftPosition 5 5 0 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 5 5 0) : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerACB) r) = rows_innerACB r := by
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

def rows_assocBAC (r : RightIndex 0 5 5) : List ℤ := rows_assocBACData.getD (rightPosition 0 5 5 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_2 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_3 : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 0 5 5) : (tripleIndices 1 4 4).map ((HexagonAtoms505.assocBAC) r) = rows_assocBAC r := by
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

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 36575260,
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

def rows_innerRightBAC (r : RightIndex 0 5 5) : List ℤ := rows_innerRightBACData.getD (rightPosition 0 5 5 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 0 5 5) : (tripleIndices 4 1 4).map ((HexagonAtoms505.innerRightBAC) r) = rows_innerRightBAC r := by
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

def rows_assocCAB (r : RightIndex 5 5 0) : List ℤ := rows_assocCABData.getD (rightPosition 5 5 0 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_2 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_3 : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 5 0) : (tripleIndices 4 1 4).map ((HexagonAtoms505.assocCAB) r) = rows_assocCAB r := by
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

def cols_right0 (r : LeftIndex 5 0 5) : List ℤ := cols_right0Data.getD (leftPosition 5 0 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_2 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_3 : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 0 5) : (tripleIndices 1 4 4).map (fun j => (right0Middle5 0 5) j r) = cols_right0 r := by
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

def cols_right1 (r : LeftIndex 5 0 5) : List ℤ := cols_right1Data.getD (leftPosition 5 0 5 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right1 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 5 0 5) : (tripleIndices 4 1 4).map (fun j => (right1Middle5 0 5) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6471460,
    decodeIntegerRow 16 3 1 15108944,
    decodeIntegerRow 16 3 1 18411312,
    decodeIntegerRow 16 3 1 7890100,
    decodeIntegerRow 16 3 1 7889104,
    decodeIntegerRow 16 3 1 18415580,
    decodeIntegerRow 16 3 1 27942260,
    decodeIntegerRow 16 3 1 36573328,
    decodeIntegerRow 16 3 1 24792816,
    decodeIntegerRow 16 3 1 7522660,
    decodeIntegerRow 16 3 1 6812620,
    decodeIntegerRow 16 3 1 27858992,
    decodeIntegerRow 16 3 1 15183140,
    decodeIntegerRow 16 3 1 36232144,
    decodeIntegerRow 16 3 1 7521712,
    decodeIntegerRow 16 3 1 24788660]

def cols_left0 (r : LeftIndex 5 0 5) : List ℤ := cols_left0Data.getD (leftPosition 5 0 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_2 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_3 : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_left0 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 0 5) : (tripleIndices 1 4 4).map (fun j => (left0Middle5 0 5) j r) = cols_left0 r := by
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

def cols_left1 (r : LeftIndex 5 0 5) : List ℤ := cols_left1Data.getD (leftPosition 5 0 5 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_left1 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 5 0 5) : (tripleIndices 4 1 4).map (fun j => (left1Middle5 0 5) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 6471460,
    decodeIntegerRow 16 3 1 15108944,
    decodeIntegerRow 16 3 1 18411312,
    decodeIntegerRow 16 3 1 7890100,
    decodeIntegerRow 16 3 1 7889104,
    decodeIntegerRow 16 3 1 18415580,
    decodeIntegerRow 16 3 1 27942260,
    decodeIntegerRow 16 3 1 36573328,
    decodeIntegerRow 16 3 1 24792816,
    decodeIntegerRow 16 3 1 7522660,
    decodeIntegerRow 16 3 1 6812620,
    decodeIntegerRow 16 3 1 27858992,
    decodeIntegerRow 16 3 1 15183140,
    decodeIntegerRow 16 3 1 36232144,
    decodeIntegerRow 16 3 1 7521712,
    decodeIntegerRow 16 3 1 24788660]

def cols_right2 (r : LeftIndex 5 0 5) : List ℤ := cols_right2Data.getD (leftPosition 5 0 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4))) = cols_right2 ((0 : Fin 1), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 0 5) : (tripleIndices 4 1 4).map (fun j => (right2Middle5 0 5) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms505.outerABC * HexagonAtoms505.assocABC = HexagonAtoms505.outerABC :=
  Matrix.mul_one (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product1_eq : HexagonAtoms505.assocBAC * HexagonAtoms505.innerABC = HexagonAtoms505.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product2_eq : HexagonAtoms505.innerRightABC * HexagonAtoms505.assocABC = HexagonAtoms505.assocABC :=
  Matrix.one_mul (m := Fin 1 × Fin 4 × Fin 4) (n := Fin 1 × Fin 4 × Fin 4) _

theorem product3_eq : HexagonAtoms505.inverseACB * right0Middle5 0 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms505.innerACB * right1Middle5 0 5 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms505.assocBAC * left0Middle5 0 5 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms505.innerRightBAC * left1Middle5 0 5 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms505.assocCAB * right2Middle5 0 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn505
