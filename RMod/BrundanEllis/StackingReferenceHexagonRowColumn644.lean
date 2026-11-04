import RMod.BrundanEllis.StackingReferenceHexagonAtoms644
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn644
open Superfusion

theorem innerACB_alias : HexagonAtoms644.innerACB = HexagonAtoms644.innerABC :=
  HexagonAtoms644.innerACB_eq.symm.trans HexagonAtoms644.innerABC_eq

theorem assocCAB_alias : HexagonAtoms644.assocCAB = HexagonAtoms644.assocBAC :=
  HexagonAtoms644.assocCAB_eq.symm.trans HexagonAtoms644.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def rows_innerRightABC (r : RightIndex 6 4 4) : List ℤ := rows_innerRightABCData.getD (rightPosition 6 4 4 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 6 4 4) : (tripleIndices 4 1 4).map ((HexagonAtoms644.innerRightABC) r) = rows_innerRightABC r := by
  fin_cases r
  · exact rows_innerRightABC_eq_0_0_0
  · exact rows_innerRightABC_eq_0_0_1
  · exact rows_innerRightABC_eq_0_0_2
  · exact rows_innerRightABC_eq_0_0_3
  · exact rows_innerRightABC_eq_1_0_0
  · exact rows_innerRightABC_eq_1_0_1
  · exact rows_innerRightABC_eq_1_0_2
  · exact rows_innerRightABC_eq_1_0_3
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_0_2
  · exact rows_innerRightABC_eq_2_0_3
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_0_2
  · exact rows_innerRightABC_eq_3_0_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21522628,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 21877654,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 26286646]

def rows_inverseACB (r : LeftIndex 6 4 4) : List ℤ := rows_inverseACBData.getD (leftPosition 6 4 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 4 4) : (tripleIndices 4 1 4).map ((HexagonAtoms644.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 35865706,
    decodeIntegerRow 16 3 1 16720708,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 16760074]

def rows_assocBCA (r : RightIndex 4 4 6) : List ℤ := rows_assocBCAData.getD (rightPosition 4 4 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 4 4 6) : (tripleIndices 4 1 4).map ((HexagonAtoms644.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def rows_assocBAC (r : RightIndex 4 6 4) : List ℤ := rows_assocBACData.getD (rightPosition 4 6 4 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_2 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_3 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_2 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_3 : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = rows_assocBAC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 4 6 4) : (tripleIndices 2 2 4).map ((HexagonAtoms644.assocBAC) r) = rows_assocBAC r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21522628,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 21877654,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 26286646]

def cols_assocABC (r : LeftIndex 6 4 4) : List ℤ := cols_assocABCData.getD (leftPosition 6 4 4 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 6 4 4) : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms644.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21524086,
    decodeIntegerRow 16 3 1 35865706,
    decodeIntegerRow 16 3 1 16720708,
    decodeIntegerRow 16 3 1 23058634,
    decodeIntegerRow 16 3 1 20814772,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 19869988,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 7167892,
    decodeIntegerRow 16 3 1 16760074]

def cols_right0 (r : LeftIndex 6 4 4) : List ℤ := cols_right0Data.getD (leftPosition 6 4 4 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 4 4) : (tripleIndices 4 1 4).map (fun j => (right0Middle6 4 4) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 21523126,
    decodeIntegerRow 16 3 1 21523252,
    decodeIntegerRow 16 3 1 21521174,
    decodeIntegerRow 16 3 1 21522628,
    decodeIntegerRow 16 3 1 7181014,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 21523306,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 21877654,
    decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 26286646]

def cols_left0 (r : LeftIndex 6 4 4) : List ℤ := cols_left0Data.getD (leftPosition 6 4 4 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 4 4) : (tripleIndices 4 1 4).map (fun j => (left0Middle6 4 4) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 76313476562,
    decodeIntegerRow 16 5 2 76196289062,
    decodeIntegerRow 16 5 2 76294726562,
    decodeIntegerRow 16 5 2 76290039062,
    decodeIntegerRow 16 5 2 76293944062,
    decodeIntegerRow 16 5 2 76293939062,
    decodeIntegerRow 16 5 2 76293914062,
    decodeIntegerRow 16 5 2 76293789062,
    decodeIntegerRow 16 5 2 76293945362,
    decodeIntegerRow 16 5 2 76293945062,
    decodeIntegerRow 16 5 2 76293945314,
    decodeIntegerRow 16 5 2 76293945302,
    decodeIntegerRow 16 5 2 75805664062,
    decodeIntegerRow 16 5 2 73852539062,
    decodeIntegerRow 16 5 2 64086914062,
    decodeIntegerRow 16 5 2 15258789062]

def cols_right2 (r : LeftIndex 6 4 4) : List ℤ := cols_right2Data.getD (leftPosition 6 4 4 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 2), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 4 4) : (tripleIndices 2 2 4).map (fun j => (right2Middle6 4 4) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms644.outerABC * HexagonAtoms644.assocABC = HexagonAtoms644.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product1_eq : HexagonAtoms644.assocBAC * HexagonAtoms644.innerABC = HexagonAtoms644.assocBAC :=
  Matrix.mul_one (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product2_eq : HexagonAtoms644.innerRightABC * HexagonAtoms644.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms644.inverseACB * right0Middle6 4 4 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms644.innerABC * right1Middle6 4 4 = right1Middle6 4 4 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms644.assocBCA * left0Middle6 4 4 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms644.innerRightBAC * left1Middle6 4 4 = left1Middle6 4 4 :=
  Matrix.one_mul (m := Fin 2 × Fin 2 × Fin 4) (n := Fin 2 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms644.assocBAC * right2Middle6 4 4 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn644
