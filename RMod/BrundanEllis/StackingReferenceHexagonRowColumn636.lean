import RMod.BrundanEllis.StackingReferenceHexagonAtoms636
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn636
open Superfusion

theorem assocBCA_alias : HexagonAtoms636.assocBCA = HexagonAtoms636.assocBAC :=
  HexagonAtoms636.assocBCA_eq.symm.trans HexagonAtoms636.assocBAC_eq

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 24631196,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 27859044,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 18253848,
    decodeIntegerRow 16 3 1 7521688,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 15183192]

def rows_inverseACB (r : LeftIndex 6 6 3) : List ℤ := rows_inverseACBData.getD (leftPosition 6 6 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 6 3) : (tripleIndices 4 2 2).map ((HexagonAtoms636.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_0_2_0
  · exact rows_inverseACB_eq_0_2_1
  · exact rows_inverseACB_eq_0_3_0
  · exact rows_inverseACB_eq_0_3_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_1_2_0
  · exact rows_inverseACB_eq_1_2_1
  · exact rows_inverseACB_eq_1_3_0
  · exact rows_inverseACB_eq_1_3_1

private def rows_innerACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921]

def rows_innerACB (r : LeftIndex 6 6 3) : List ℤ := rows_innerACBData.getD (leftPosition 6 6 3 r) []

private theorem rows_innerACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerACB_data (r : LeftIndex 6 6 3) : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerACB) r) = rows_innerACB r := by
  fin_cases r
  · exact rows_innerACB_eq_0_0_0
  · exact rows_innerACB_eq_0_0_1
  · exact rows_innerACB_eq_0_1_0
  · exact rows_innerACB_eq_0_1_1
  · exact rows_innerACB_eq_0_2_0
  · exact rows_innerACB_eq_0_2_1
  · exact rows_innerACB_eq_0_3_0
  · exact rows_innerACB_eq_0_3_1
  · exact rows_innerACB_eq_1_0_0
  · exact rows_innerACB_eq_1_0_1
  · exact rows_innerACB_eq_1_1_0
  · exact rows_innerACB_eq_1_1_1
  · exact rows_innerACB_eq_1_2_0
  · exact rows_innerACB_eq_1_2_1
  · exact rows_innerACB_eq_1_3_0
  · exact rows_innerACB_eq_1_3_1

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 7890076,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 24635352,
    decodeIntegerRow 16 3 1 35157592,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 15183192,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 35525032,
    decodeIntegerRow 16 3 1 24792872,
    decodeIntegerRow 16 3 1 6814564,
    decodeIntegerRow 16 3 1 15187676]

def rows_assocBAC (r : RightIndex 3 6 6) : List ℤ := rows_assocBACData.getD (rightPosition 3 6 6 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_2_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_0 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_3_1 : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 3 6 6) : (tripleIndices 4 2 2).map ((HexagonAtoms636.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_0_2_0
  · exact rows_assocBAC_eq_0_2_1
  · exact rows_assocBAC_eq_0_3_0
  · exact rows_assocBAC_eq_0_3_1
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_1_2_0
  · exact rows_assocBAC_eq_1_2_1
  · exact rows_assocBAC_eq_1_3_0
  · exact rows_assocBAC_eq_1_3_1

private def rows_innerRightBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921]

def rows_innerRightBAC (r : RightIndex 3 6 6) : List ℤ := rows_innerRightBACData.getD (rightPosition 3 6 6 r) []

private theorem rows_innerRightBAC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightBAC_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightBAC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightBAC_data (r : RightIndex 3 6 6) : (tripleIndices 2 4 2).map ((HexagonAtoms636.innerRightBAC) r) = rows_innerRightBAC r := by
  fin_cases r
  · exact rows_innerRightBAC_eq_0_0_0
  · exact rows_innerRightBAC_eq_0_0_1
  · exact rows_innerRightBAC_eq_0_1_0
  · exact rows_innerRightBAC_eq_0_1_1
  · exact rows_innerRightBAC_eq_0_2_0
  · exact rows_innerRightBAC_eq_0_2_1
  · exact rows_innerRightBAC_eq_0_3_0
  · exact rows_innerRightBAC_eq_0_3_1
  · exact rows_innerRightBAC_eq_1_0_0
  · exact rows_innerRightBAC_eq_1_0_1
  · exact rows_innerRightBAC_eq_1_1_0
  · exact rows_innerRightBAC_eq_1_1_1
  · exact rows_innerRightBAC_eq_1_2_0
  · exact rows_innerRightBAC_eq_1_2_1
  · exact rows_innerRightBAC_eq_1_3_0
  · exact rows_innerRightBAC_eq_1_3_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320]

def rows_assocCAB (r : RightIndex 6 6 3) : List ℤ := rows_assocCABData.getD (rightPosition 6 6 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 6 3) : (tripleIndices 2 4 2).map ((HexagonAtoms636.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 23058526,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 26323826,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 19869934,
    decodeIntegerRow 16 3 1 16762262,
    decodeIntegerRow 16 3 1 7181746,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22231714]

def cols_right0 (r : LeftIndex 6 3 6) : List ℤ := cols_right0Data.getD (leftPosition 6 3 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 3 6) : (tripleIndices 4 2 2).map (fun j => (right0Middle6 3 6) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 12837665552,
    decodeIntegerRow 16 5 2 63700045360,
    decodeIntegerRow 16 5 2 88106607864,
    decodeIntegerRow 16 5 2 134906478072,
    decodeIntegerRow 16 5 2 17681478072,
    decodeIntegerRow 16 5 2 64481607864,
    decodeIntegerRow 16 5 2 63700345264,
    decodeIntegerRow 16 5 2 12837725072,
    decodeIntegerRow 16 5 2 87919107760,
    decodeIntegerRow 16 5 2 134868977552,
    decodeIntegerRow 16 5 2 12797040072,
    decodeIntegerRow 16 5 2 63496920264,
    decodeIntegerRow 16 5 2 89090670264,
    decodeIntegerRow 16 5 2 139790790072,
    decodeIntegerRow 16 5 2 134868913072,
    decodeIntegerRow 16 5 2 87918782864]

def cols_right1 (r : LeftIndex 6 3 6) : List ℤ := cols_right1Data.getD (leftPosition 6 3 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 6 3 6) : (tripleIndices 2 4 2).map (fun j => (right1Middle6 3 6) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_1_0
  · exact cols_right1_eq_2_1_1
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_1_0
  · exact cols_right1_eq_3_1_1

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 23058526,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 26323826,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 20814538,
    decodeIntegerRow 16 3 1 19869934,
    decodeIntegerRow 16 3 1 16762262,
    decodeIntegerRow 16 3 1 7181746,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22231714]

def cols_left0 (r : LeftIndex 6 3 6) : List ℤ := cols_left0Data.getD (leftPosition 6 3 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 3 6) : (tripleIndices 4 2 2).map (fun j => (left0Middle6 3 6) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 26642876,
    decodeIntegerRow 16 3 1 17111928,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 34329592,
    decodeIntegerRow 16 3 1 25929912,
    decodeIntegerRow 16 3 1 26639004,
    decodeIntegerRow 16 3 1 37400356,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 27036552,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 5515192,
    decodeIntegerRow 16 3 1 8822044,
    decodeIntegerRow 16 3 1 17431716]

def cols_left1 (r : LeftIndex 6 3 6) : List ℤ := cols_left1Data.getD (leftPosition 6 3 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 6 3 6) : (tripleIndices 2 4 2).map (fun j => (left1Middle6 3 6) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_1_0
  · exact cols_left1_eq_2_1_1
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_1_0
  · exact cols_left1_eq_3_1_1

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 139790787552,
    decodeIntegerRow 16 5 2 89090657760,
    decodeIntegerRow 16 5 2 64668795360,
    decodeIntegerRow 16 5 2 17718915552,
    decodeIntegerRow 16 5 2 134868915552,
    decodeIntegerRow 16 5 2 87918795360,
    decodeIntegerRow 16 5 2 89090982864,
    decodeIntegerRow 16 5 2 139790853072,
    decodeIntegerRow 16 5 2 88106595360,
    decodeIntegerRow 16 5 2 134906475552,
    decodeIntegerRow 16 5 2 12837727552,
    decodeIntegerRow 16 5 2 63700357760,
    decodeIntegerRow 16 5 2 88887857760,
    decodeIntegerRow 16 5 2 139750227552,
    decodeIntegerRow 16 5 2 134906415072,
    decodeIntegerRow 16 5 2 88106295264]

def cols_right2 (r : LeftIndex 6 3 6) : List ℤ := cols_right2Data.getD (leftPosition 6 3 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 3 6) : (tripleIndices 2 4 2).map (fun j => (right2Middle6 3 6) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1

theorem product0_eq : HexagonAtoms636.outerABC * HexagonAtoms636.assocABC = HexagonAtoms636.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product1_eq : HexagonAtoms636.assocBAC * HexagonAtoms636.innerABC = HexagonAtoms636.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product2_eq : HexagonAtoms636.innerRightABC * HexagonAtoms636.assocABC = HexagonAtoms636.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product3_eq : HexagonAtoms636.inverseACB * right0Middle6 3 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms636.innerACB * right1Middle6 3 6 = rowColumnMul rows_innerACB cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerACB_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms636.assocBAC * left0Middle6 3 6 = rowColumnMul rows_assocBAC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms636.innerRightBAC * left1Middle6 3 6 = rowColumnMul rows_innerRightBAC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightBAC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms636.assocCAB * right2Middle6 3 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn636
