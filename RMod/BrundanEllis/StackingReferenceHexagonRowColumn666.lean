import RMod.BrundanEllis.StackingReferenceHexagonAtoms666
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn666
open Superfusion

theorem assocBAC_alias : HexagonAtoms666.assocBAC = HexagonAtoms666.assocABC :=
  HexagonAtoms666.assocBAC_eq.symm.trans HexagonAtoms666.assocABC_eq

theorem innerACB_alias : HexagonAtoms666.innerACB = HexagonAtoms666.innerABC :=
  HexagonAtoms666.innerACB_eq.symm.trans HexagonAtoms666.innerABC_eq

theorem assocBCA_alias : HexagonAtoms666.assocBCA = HexagonAtoms666.assocABC :=
  HexagonAtoms666.assocBCA_eq.symm.trans HexagonAtoms666.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms666.innerRightBAC = HexagonAtoms666.innerRightABC :=
  HexagonAtoms666.innerRightBAC_eq.symm.trans HexagonAtoms666.innerRightABC_eq

theorem assocCAB_alias : HexagonAtoms666.assocCAB = HexagonAtoms666.assocABC :=
  HexagonAtoms666.assocCAB_eq.symm.trans HexagonAtoms666.assocABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043]

def rows_assocABC (r : RightIndex 6 6 6) : List ℤ := rows_assocABCData.getD (rightPosition 6 6 6 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 6 6 6) : (tripleIndices 2 2 4).map ((HexagonAtoms666.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_0_1_2
  · exact rows_assocABC_eq_0_1_3
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_0_2
  · exact rows_assocABC_eq_1_0_3
  · exact rows_assocABC_eq_1_1_0
  · exact rows_assocABC_eq_1_1_1
  · exact rows_assocABC_eq_1_1_2
  · exact rows_assocABC_eq_1_1_3

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def rows_innerRightABC (r : RightIndex 6 6 6) : List ℤ := rows_innerRightABCData.getD (rightPosition 6 6 6 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 6 6 6) : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_1_2
  · exact rows_innerRightABC_eq_0_1_3
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_1_1_2
  · exact rows_innerRightABC_eq_1_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361]

def rows_inverseACB (r : LeftIndex 6 6 6) : List ℤ := rows_inverseACBData.getD (leftPosition 6 6 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map ((HexagonAtoms666.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409]

def rows_innerABC (r : LeftIndex 6 6 6) : List ℤ := rows_innerABCData.getD (leftPosition 6 6 6 r) []

private theorem rows_innerABC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_innerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_innerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_innerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_innerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_innerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_innerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_innerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_innerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerABC_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map ((HexagonAtoms666.innerABC) r) = rows_innerABC r := by
  fin_cases r
  · exact rows_innerABC_eq_0_0_0
  · exact rows_innerABC_eq_0_0_1
  · exact rows_innerABC_eq_0_0_2
  · exact rows_innerABC_eq_0_0_3
  · exact rows_innerABC_eq_0_1_0
  · exact rows_innerABC_eq_0_1_1
  · exact rows_innerABC_eq_0_1_2
  · exact rows_innerABC_eq_0_1_3
  · exact rows_innerABC_eq_1_0_0
  · exact rows_innerABC_eq_1_0_1
  · exact rows_innerABC_eq_1_0_2
  · exact rows_innerABC_eq_1_0_3
  · exact rows_innerABC_eq_1_1_0
  · exact rows_innerABC_eq_1_1_1
  · exact rows_innerABC_eq_1_1_2
  · exact rows_innerABC_eq_1_1_3

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311]

def cols_innerABC (r : LeftIndex 6 6 6) : List ℤ := cols_innerABCData.getD (leftPosition 6 6 6 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_0_2
  · exact cols_innerABC_eq_0_0_3
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_1_2
  · exact cols_innerABC_eq_0_1_3
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_0_2
  · exact cols_innerABC_eq_1_0_3
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_1_1_2
  · exact cols_innerABC_eq_1_1_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361]

def cols_assocABC (r : LeftIndex 6 6 6) : List ℤ := cols_assocABCData.getD (leftPosition 6 6 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map (fun j => (HexagonAtoms666.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333]

def cols_right0 (r : LeftIndex 6 6 6) : List ℤ := cols_right0Data.getD (leftPosition 6 6 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map (fun j => (right0Middle6 6 6) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 22054801]

def cols_right1 (r : LeftIndex 6 6 6) : List ℤ := cols_right1Data.getD (leftPosition 6 6 6 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map (fun j => (right1Middle6 6 6) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_0_2
  · exact cols_right1_eq_0_0_3
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_1_2
  · exact cols_right1_eq_0_1_3
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_0_2
  · exact cols_right1_eq_1_0_3
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_1_1_2
  · exact cols_right1_eq_1_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361]

def cols_left0 (r : LeftIndex 6 6 6) : List ℤ := cols_left0Data.getD (leftPosition 6 6 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map (fun j => (left0Middle6 6 6) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919]

def cols_left1 (r : LeftIndex 6 6 6) : List ℤ := cols_left1Data.getD (leftPosition 6 6 6 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left1 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map (fun j => (left1Middle6 6 6) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_0_2
  · exact cols_left1_eq_0_0_3
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_1_2
  · exact cols_left1_eq_0_1_3
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_0_2
  · exact cols_left1_eq_1_0_3
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_1_1_2
  · exact cols_left1_eq_1_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043]

def cols_right2 (r : LeftIndex 6 6 6) : List ℤ := cols_right2Data.getD (leftPosition 6 6 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 6 6) : (tripleIndices 2 2 4).map (fun j => (right2Middle6 6 6) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms666.outerABC * HexagonAtoms666.assocABC = HexagonAtoms666.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product1_eq : HexagonAtoms666.assocABC * HexagonAtoms666.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms666.innerRightABC * HexagonAtoms666.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms666.inverseACB * right0Middle6 6 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms666.innerABC * right1Middle6 6 6 = rowColumnMul rows_innerABC cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerABC_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms666.assocABC * left0Middle6 6 6 = rowColumnMul rows_assocABC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms666.innerRightABC * left1Middle6 6 6 = rowColumnMul rows_innerRightABC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms666.assocABC * right2Middle6 6 6 = rowColumnMul rows_assocABC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn666
