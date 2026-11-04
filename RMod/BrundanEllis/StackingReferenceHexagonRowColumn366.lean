import RMod.BrundanEllis.StackingReferenceHexagonAtoms366
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn366
open Superfusion

theorem innerACB_alias : HexagonAtoms366.innerACB = HexagonAtoms366.innerABC :=
  HexagonAtoms366.innerACB_eq.symm.trans HexagonAtoms366.innerABC_eq

theorem assocCAB_alias : HexagonAtoms366.assocCAB = HexagonAtoms366.assocBAC :=
  HexagonAtoms366.assocCAB_eq.symm.trans HexagonAtoms366.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523117,
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

def rows_innerRightABC (r : RightIndex 3 6 6) : List ℤ := rows_innerRightABCData.getD (rightPosition 3 6 6 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 3 6 6) : (tripleIndices 2 4 2).map ((HexagonAtoms366.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_1_0
  · exact rows_innerRightABC_eq_0_1_1
  · exact rows_innerRightABC_eq_0_2_0
  · exact rows_innerRightABC_eq_0_2_1
  · exact rows_innerRightABC_eq_0_3_0
  · exact rows_innerRightABC_eq_0_3_1
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_1_0
  · exact rows_innerRightABC_eq_1_1_1
  · exact rows_innerRightABC_eq_1_2_0
  · exact rows_innerRightABC_eq_1_2_1
  · exact rows_innerRightABC_eq_1_3_0
  · exact rows_innerRightABC_eq_1_3_1

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
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

def rows_inverseACB (r : LeftIndex 3 6 6) : List ℤ := rows_inverseACBData.getD (leftPosition 3 6 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 6 6) : (tripleIndices 2 4 2).map ((HexagonAtoms366.inverseACB) r) = rows_inverseACB r := by
  fin_cases r
  · exact rows_inverseACB_eq_0_0_0
  · exact rows_inverseACB_eq_0_0_1
  · exact rows_inverseACB_eq_0_1_0
  · exact rows_inverseACB_eq_0_1_1
  · exact rows_inverseACB_eq_1_0_0
  · exact rows_inverseACB_eq_1_0_1
  · exact rows_inverseACB_eq_1_1_0
  · exact rows_inverseACB_eq_1_1_1
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
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

def rows_assocBCA (r : RightIndex 6 6 3) : List ℤ := rows_assocBCAData.getD (rightPosition 6 6 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 6 3) : (tripleIndices 2 4 2).map ((HexagonAtoms366.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_1_0
  · exact rows_assocBCA_eq_2_1_1
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_1_0
  · exact rows_assocBCA_eq_3_1_1

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 21169318,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26328198,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7168618,
    decodeIntegerRow 16 3 1 21168814,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 35866438,
    decodeIntegerRow 16 3 1 26288834,
    decodeIntegerRow 16 3 1 19870042,
    decodeIntegerRow 16 3 1 20815006]

def rows_assocBAC (r : RightIndex 6 3 6) : List ℤ := rows_assocBACData.getD (rightPosition 6 3 6 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 6 3 6) : (tripleIndices 4 2 2).map ((HexagonAtoms366.assocBAC) r) = rows_assocBAC r := by
  fin_cases r
  · exact rows_assocBAC_eq_0_0_0
  · exact rows_assocBAC_eq_0_0_1
  · exact rows_assocBAC_eq_0_1_0
  · exact rows_assocBAC_eq_0_1_1
  · exact rows_assocBAC_eq_1_0_0
  · exact rows_assocBAC_eq_1_0_1
  · exact rows_assocBAC_eq_1_1_0
  · exact rows_assocBAC_eq_1_1_1
  · exact rows_assocBAC_eq_2_0_0
  · exact rows_assocBAC_eq_2_0_1
  · exact rows_assocBAC_eq_2_1_0
  · exact rows_assocBAC_eq_2_1_1
  · exact rows_assocBAC_eq_3_0_0
  · exact rows_assocBAC_eq_3_0_1
  · exact rows_assocBAC_eq_3_1_0
  · exact rows_assocBAC_eq_3_1_1

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
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

def cols_assocABC (r : LeftIndex 3 6 6) : List ℤ := cols_assocABCData.getD (leftPosition 3 6 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 6 6) : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms366.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
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

def cols_right0 (r : LeftIndex 3 6 6) : List ℤ := cols_right0Data.getD (leftPosition 3 6 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 6 6) : (tripleIndices 2 4 2).map (fun j => (right0Middle3 6 6) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
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

def cols_left0 (r : LeftIndex 3 6 6) : List ℤ := cols_left0Data.getD (leftPosition 3 6 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 6 6) : (tripleIndices 2 4 2).map (fun j => (left0Middle3 6 6) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 9 4 936663610572472,
    decodeIntegerRow 16 9 4 927514288096888,
    decodeIntegerRow 16 9 4 102945391734712,
    decodeIntegerRow 16 9 4 835001355792248,
    decodeIntegerRow 16 9 4 1018018794795848,
    decodeIntegerRow 16 9 4 1750074792865672,
    decodeIntegerRow 16 9 4 927514288569928,
    decodeIntegerRow 16 9 4 936663610630792,
    decodeIntegerRow 16 9 4 925254851805688,
    decodeIntegerRow 16 9 4 916328683951672,
    decodeIntegerRow 16 9 4 835004493419912,
    decodeIntegerRow 16 9 4 102945740360008,
    decodeIntegerRow 16 9 4 102945736108408,
    decodeIntegerRow 16 9 4 835004455156152,
    decodeIntegerRow 16 9 4 936691504853512,
    decodeIntegerRow 16 9 4 927765336574408]

def cols_right2 (r : LeftIndex 3 6 6) : List ℤ := cols_right2Data.getD (leftPosition 3 6 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 6 6) : (tripleIndices 4 2 2).map (fun j => (right2Middle3 6 6) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms366.outerABC * HexagonAtoms366.assocABC = HexagonAtoms366.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product1_eq : HexagonAtoms366.assocBAC * HexagonAtoms366.innerABC = HexagonAtoms366.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product2_eq : HexagonAtoms366.innerRightABC * HexagonAtoms366.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms366.inverseACB * right0Middle3 6 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms366.innerABC * right1Middle3 6 6 = right1Middle3 6 6 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product5_eq : HexagonAtoms366.assocBCA * left0Middle3 6 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms366.innerRightBAC * left1Middle3 6 6 = left1Middle3 6 6 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product7_eq : HexagonAtoms366.assocBAC * right2Middle3 6 6 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn366
