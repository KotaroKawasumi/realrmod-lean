import RMod.BrundanEllis.StackingReferenceHexagonAtoms626
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn626
open Superfusion

theorem assocBCA_alias : HexagonAtoms626.assocBCA = HexagonAtoms626.assocBAC :=
  HexagonAtoms626.assocBCA_eq.symm.trans HexagonAtoms626.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 35865706]

def rows_inverseACB (r : LeftIndex 6 6 2) : List ℤ := rows_inverseACBData.getD (leftPosition 6 6 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 6 2) : (tripleIndices 4 1 4).map ((HexagonAtoms626.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409]

def rows_innerACB (r : LeftIndex 6 6 2) : List ℤ := rows_innerACBData.getD (leftPosition 6 6 2 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 6 6 2) : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_0_2
  · exact rows_innerACB_eq_0_0_3
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_1_2
  · exact rows_innerACB_eq_0_1_3
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_0_2
  · exact rows_innerACB_eq_1_0_3
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_1_1_2
  · exact rows_innerACB_eq_1_1_3

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 16760074,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 16720708,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 21523126]

def rows_assocBAC (r : RightIndex 2 6 6) : List ℤ := rows_assocBACData.getD (rightPosition 2 6 6 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 2 6 6) : (tripleIndices 4 1 4).map ((HexagonAtoms626.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_0_2
  · exact rows_assocBAC_eq_0_0_3
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_1_2
  · exact rows_assocBAC_eq_0_1_3
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_0_2
  · exact rows_assocBAC_eq_1_0_3
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_1_2
  · exact rows_assocBAC_eq_1_1_3

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409]

def rows_innerRightBAC (r : RightIndex 2 6 6) : List ℤ := rows_innerRightBACData.getD (rightPosition 2 6 6 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 2 6 6) : (tripleIndices 2 2 4).map ((HexagonAtoms626.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_0_2
  · exact rows_innerRightBAC_eq_0_0_3
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_1_2
  · exact rows_innerRightBAC_eq_0_1_3
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_0_2
  · exact rows_innerRightBAC_eq_1_0_3
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_1_1_2
  · exact rows_innerRightBAC_eq_1_1_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35871538]

def rows_assocCAB (r : RightIndex 6 6 2) : List ℤ := rows_assocCABData.getD (rightPosition 6 6 2 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 6 2) : (tripleIndices 2 2 4).map ((HexagonAtoms626.assocCAB) r) = rows_assocCAB r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 19988140,
    decodeIntegerRow 16 3 1 20815024,
    decodeIntegerRow 16 3 1 7181740,
    decodeIntegerRow 16 3 1 16722896,
    decodeIntegerRow 16 3 1 16718520,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 20814520,
    decodeIntegerRow 16 3 1 23058688,
    decodeIntegerRow 16 3 1 21877888,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 7168624,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 19870096,
    decodeIntegerRow 16 3 1 21877420]

def cols_right0 (r : LeftIndex 6 2 6) : List ℤ := cols_right0Data.getD (leftPosition 6 2 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 2 6) : (tripleIndices 4 1 4).map (fun j => (right0Middle6 2 6) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 73852539012,
    decodeIntegerRow 16 5 2 75805664312,
    decodeIntegerRow 16 5 2 15258789060,
    decodeIntegerRow 16 5 2 64086914072,
    decodeIntegerRow 16 5 2 64086914052,
    decodeIntegerRow 16 5 2 137329101560,
    decodeIntegerRow 16 5 2 75805663812,
    decodeIntegerRow 16 5 2 78735351512,
    decodeIntegerRow 16 5 2 76274407812,
    decodeIntegerRow 16 5 2 76391600312,
    decodeIntegerRow 16 5 2 76293007812,
    decodeIntegerRow 16 5 2 76297820312,
    decodeIntegerRow 16 5 2 76297882812,
    decodeIntegerRow 16 5 2 76294570312,
    decodeIntegerRow 16 5 2 76391602812,
    decodeIntegerRow 16 5 2 76313470312]

def cols_right1 (r : LeftIndex 6 2 6) : List ℤ := cols_right1Data.getD (leftPosition 6 2 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 6 2 6) : (tripleIndices 2 2 4).map (fun j => (right1Middle6 2 6) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_0_2
  · exact cols_right1_eq_2_0_3
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_0_2
  · exact cols_right1_eq_3_0_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 19988140,
    decodeIntegerRow 16 3 1 20815024,
    decodeIntegerRow 16 3 1 7181740,
    decodeIntegerRow 16 3 1 16722896,
    decodeIntegerRow 16 3 1 16718520,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 20814520,
    decodeIntegerRow 16 3 1 23058688,
    decodeIntegerRow 16 3 1 21877888,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 26288832,
    decodeIntegerRow 16 3 1 35879560,
    decodeIntegerRow 16 3 1 7168624,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 19870096,
    decodeIntegerRow 16 3 1 21877420]

def cols_left0 (r : LeftIndex 6 2 6) : List ℤ := cols_left0Data.getD (leftPosition 6 2 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 2 6) : (tripleIndices 4 1 4).map (fun j => (left0Middle6 2 6) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 23117692,
    decodeIntegerRow 16 3 1 22054774,
    decodeIntegerRow 16 3 1 35872268,
    decodeIntegerRow 16 3 1 26306326,
    decodeIntegerRow 16 3 1 26306332,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 21582652,
    decodeIntegerRow 16 3 1 21346294,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21504406,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21518986,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 21464554]

def cols_left1 (r : LeftIndex 6 2 6) : List ℤ := cols_left1Data.getD (leftPosition 6 2 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 6 2 6) : (tripleIndices 2 2 4).map (fun j => (left1Middle6 2 6) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_0_2
  · exact cols_left1_eq_2_0_3
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_0_2
  · exact cols_left1_eq_3_0_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76294726572,
    decodeIntegerRow 16 5 2 76297851564,
    decodeIntegerRow 16 5 2 76313476812,
    decodeIntegerRow 16 5 2 76391601612,
    decodeIntegerRow 16 5 2 76391601512,
    decodeIntegerRow 16 5 2 76274414312,
    decodeIntegerRow 16 5 2 76297851560,
    decodeIntegerRow 16 5 2 76293164072,
    decodeIntegerRow 16 5 2 15258757812,
    decodeIntegerRow 16 5 2 88501132812,
    decodeIntegerRow 16 5 2 73852537812,
    decodeIntegerRow 16 5 2 76782232812,
    decodeIntegerRow 16 5 2 76782220312,
    decodeIntegerRow 16 5 2 78735350312,
    decodeIntegerRow 16 5 2 88500820312,
    decodeIntegerRow 16 5 2 137329070312]

def cols_right2 (r : LeftIndex 6 2 6) : List ℤ := cols_right2Data.getD (leftPosition 6 2 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 2 6) : (tripleIndices 2 2 4).map (fun j => (right2Middle6 2 6) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms626.outerABC * HexagonAtoms626.assocABC = HexagonAtoms626.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product1_eq : HexagonAtoms626.assocBAC * HexagonAtoms626.innerABC = HexagonAtoms626.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product2_eq : HexagonAtoms626.innerRightABC * HexagonAtoms626.assocABC = HexagonAtoms626.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms626.inverseACB * right0Middle6 2 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms626.innerACB * right1Middle6 2 6 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms626.assocBAC * left0Middle6 2 6 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms626.innerRightBAC * left1Middle6 2 6 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms626.assocCAB * right2Middle6 2 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn626
