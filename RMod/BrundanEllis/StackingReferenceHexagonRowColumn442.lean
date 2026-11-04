import RMod.BrundanEllis.StackingReferenceHexagonAtoms442
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn442
open Superfusion

theorem assocBAC_alias : HexagonAtoms442.assocBAC = HexagonAtoms442.assocABC :=
  HexagonAtoms442.assocBAC_eq.symm.trans HexagonAtoms442.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms442.innerRightBAC = HexagonAtoms442.innerRightABC :=
  HexagonAtoms442.innerRightBAC_eq.symm.trans HexagonAtoms442.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 21877654,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 21525546,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 21523108,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 35865706,
    decodeIntegerRow 16 3 1 26286646,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 21523594,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21522628]

def rows_assocABC (r : RightIndex 4 4 2) : List ℤ := rows_assocABCData.getD (rightPosition 4 4 2 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 4 4 2) : (tripleIndices 4 1 4).map ((HexagonAtoms442.assocABC) r) = rows_assocABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523117]

def rows_inverseACB (r : LeftIndex 4 2 4) : List ℤ := rows_inverseACBData.getD (leftPosition 4 2 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 2 4) : (tripleIndices 2 2 4).map ((HexagonAtoms442.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523117]

def rows_assocBCA (r : RightIndex 4 2 4) : List ℤ := rows_assocBCAData.getD (rightPosition 4 2 4 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 4 2 4) : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21529912]

def rows_assocCAB (r : RightIndex 2 4 4) : List ℤ := rows_assocCABData.getD (rightPosition 2 4 4 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 2 4 4) : (tripleIndices 2 2 4).map ((HexagonAtoms442.assocCAB) r) = rows_assocCAB r := by
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

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def cols_innerABC (r : LeftIndex 4 4 2) : List ℤ := cols_innerABCData.getD (leftPosition 4 4 2 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 4 4 2) : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms442.innerABC) j r) = cols_innerABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21529912]

def cols_right0 (r : LeftIndex 4 4 2) : List ℤ := cols_right0Data.getD (leftPosition 4 4 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 4 2) : (tripleIndices 2 2 4).map (fun j => (right0Middle4 4 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 26306248,
    decodeIntegerRow 16 3 1 7174210,
    decodeIntegerRow 16 3 1 20991190,
    decodeIntegerRow 16 3 1 23115496,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21529912]

def cols_left0 (r : LeftIndex 4 4 2) : List ℤ := cols_left0Data.getD (leftPosition 4 4 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 4 2) : (tripleIndices 2 2 4).map (fun j => (left0Middle4 4 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 3 1 16740472,
    decodeIntegerRow 16 3 1 35872510,
    decodeIntegerRow 16 3 1 22055530,
    decodeIntegerRow 16 3 1 19931224,
    decodeIntegerRow 16 3 1 19926850,
    decodeIntegerRow 16 3 1 22054072,
    decodeIntegerRow 16 3 1 7174696,
    decodeIntegerRow 16 3 1 26306410,
    decodeIntegerRow 16 3 1 21516790,
    decodeIntegerRow 16 3 1 21503704,
    decodeIntegerRow 16 3 1 21464312,
    decodeIntegerRow 16 3 1 21346210,
    decodeIntegerRow 16 3 1 21346216,
    decodeIntegerRow 16 3 1 21464310,
    decodeIntegerRow 16 3 1 21543070,
    decodeIntegerRow 16 3 1 21529912]

def cols_right2 (r : LeftIndex 4 4 2) : List ℤ := cols_right2Data.getD (leftPosition 4 4 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 4 2) : (tripleIndices 2 2 4).map (fun j => (right2Middle4 4 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms442.outerABC * HexagonAtoms442.assocABC = HexagonAtoms442.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product1_eq : HexagonAtoms442.assocABC * HexagonAtoms442.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms442.innerRightABC * HexagonAtoms442.assocABC = HexagonAtoms442.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product3_eq : HexagonAtoms442.inverseACB * right0Middle4 4 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms442.innerACB * right1Middle4 4 2 = right1Middle4 4 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product5_eq : HexagonAtoms442.assocBCA * left0Middle4 4 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms442.innerRightABC * left1Middle4 4 2 = left1Middle4 4 2 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product7_eq : HexagonAtoms442.assocCAB * right2Middle4 4 2 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn442
