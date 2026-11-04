import RMod.BrundanEllis.StackingReferenceHexagonAtoms522
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn522
open Superfusion

theorem innerACB_alias : HexagonAtoms522.innerACB = HexagonAtoms522.innerABC :=
  HexagonAtoms522.innerACB_eq.symm.trans HexagonAtoms522.innerABC_eq

theorem assocCAB_alias : HexagonAtoms522.assocCAB = HexagonAtoms522.assocBAC :=
  HexagonAtoms522.assocCAB_eq.symm.trans HexagonAtoms522.assocBAC_eq

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037]

def rows_innerRightABC (r : RightIndex 5 2 2) : List ℤ := rows_innerRightABCData.getD (rightPosition 5 2 2 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 5 2 2) : (tripleIndices 2 4 2).map ((HexagonAtoms522.innerRightABC) r) = rows_innerRightABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 26325760,
    decodeIntegerRow 16 3 1 35865760,
    decodeIntegerRow 16 3 1 19869256,
    decodeIntegerRow 16 3 1 21875468,
    decodeIntegerRow 16 3 1 21879840,
    decodeIntegerRow 16 3 1 23176000,
    decodeIntegerRow 16 3 1 35865652,
    decodeIntegerRow 16 3 1 16720456,
    decodeIntegerRow 16 3 1 7167784,
    decodeIntegerRow 16 3 1 26286412,
    decodeIntegerRow 16 3 1 22229760,
    decodeIntegerRow 16 3 1 23059360,
    decodeIntegerRow 16 3 1 19988812,
    decodeIntegerRow 16 3 1 22234136,
    decodeIntegerRow 16 3 1 16759840,
    decodeIntegerRow 16 3 1 7168000]

def rows_inverseACB (r : LeftIndex 5 2 2) : List ℤ := rows_inverseACBData.getD (leftPosition 5 2 2 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 2 2) : (tripleIndices 2 4 2).map ((HexagonAtoms522.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
    decodeIntegerRow 16 3 1 19988818,
    decodeIntegerRow 16 3 1 7167946,
    decodeIntegerRow 16 3 1 26286898,
    decodeIntegerRow 16 3 1 26286394,
    decodeIntegerRow 16 3 1 35878882,
    decodeIntegerRow 16 3 1 19987354,
    decodeIntegerRow 16 3 1 22229762,
    decodeIntegerRow 16 3 1 23177458,
    decodeIntegerRow 16 3 1 21171254,
    decodeIntegerRow 16 3 1 26325778,
    decodeIntegerRow 16 3 1 35865814,
    decodeIntegerRow 16 3 1 7181122,
    decodeIntegerRow 16 3 1 26326246,
    decodeIntegerRow 16 3 1 21879842,
    decodeIntegerRow 16 3 1 23176006]

def rows_assocBCA (r : RightIndex 2 2 5) : List ℤ := rows_assocBCAData.getD (rightPosition 2 2 5 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 2 2 5) : (tripleIndices 2 4 2).map ((HexagonAtoms522.assocBCA) r) = rows_assocBCA r := by
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

private def rows_assocBACData : List (List ℤ) := [decodeIntegerRow 16 3 1 19869934,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 16762262,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 23058526,
    decodeIntegerRow 16 3 1 26323826,
    decodeIntegerRow 16 3 1 35866438,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 20815006]

def rows_assocBAC (r : RightIndex 2 5 2) : List ℤ := rows_assocBACData.getD (rightPosition 2 5 2 r) []

private theorem rows_assocBAC_eq_0_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_0_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_1_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_2_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_0_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_0 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBAC_eq_3_1_1 : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = rows_assocBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBAC_data (r : RightIndex 2 5 2) : (tripleIndices 4 2 2).map ((HexagonAtoms522.assocBAC) r) = rows_assocBAC r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 26325760,
    decodeIntegerRow 16 3 1 35865760,
    decodeIntegerRow 16 3 1 19869256,
    decodeIntegerRow 16 3 1 21875468,
    decodeIntegerRow 16 3 1 21879840,
    decodeIntegerRow 16 3 1 23176000,
    decodeIntegerRow 16 3 1 35865652,
    decodeIntegerRow 16 3 1 16720456,
    decodeIntegerRow 16 3 1 7167784,
    decodeIntegerRow 16 3 1 26286412,
    decodeIntegerRow 16 3 1 22229760,
    decodeIntegerRow 16 3 1 23059360,
    decodeIntegerRow 16 3 1 19988812,
    decodeIntegerRow 16 3 1 22234136,
    decodeIntegerRow 16 3 1 16759840,
    decodeIntegerRow 16 3 1 7168000]

def cols_assocABC (r : LeftIndex 5 2 2) : List ℤ := cols_assocABCData.getD (leftPosition 5 2 2 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 2 2) : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms522.assocABC) j r) = cols_assocABC r := by
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

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 22234134,
    decodeIntegerRow 16 3 1 23057902,
    decodeIntegerRow 16 3 1 35878774,
    decodeIntegerRow 16 3 1 16759822,
    decodeIntegerRow 16 3 1 16760326,
    decodeIntegerRow 16 3 1 7167838,
    decodeIntegerRow 16 3 1 23059366,
    decodeIntegerRow 16 3 1 20816958,
    decodeIntegerRow 16 3 1 19869262,
    decodeIntegerRow 16 3 1 21875466,
    decodeIntegerRow 16 3 1 16720942,
    decodeIntegerRow 16 3 1 7180906,
    decodeIntegerRow 16 3 1 35865598,
    decodeIntegerRow 16 3 1 16720474,
    decodeIntegerRow 16 3 1 21166878,
    decodeIntegerRow 16 3 1 19870714]

def cols_right0 (r : LeftIndex 5 2 2) : List ℤ := cols_right0Data.getD (leftPosition 5 2 2 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 2 2) : (tripleIndices 2 4 2).map (fun j => (right0Middle5 2 2) j r) = cols_right0 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 26325760,
    decodeIntegerRow 16 3 1 35865760,
    decodeIntegerRow 16 3 1 19869256,
    decodeIntegerRow 16 3 1 21875468,
    decodeIntegerRow 16 3 1 21879840,
    decodeIntegerRow 16 3 1 23176000,
    decodeIntegerRow 16 3 1 35865652,
    decodeIntegerRow 16 3 1 16720456,
    decodeIntegerRow 16 3 1 7167784,
    decodeIntegerRow 16 3 1 26286412,
    decodeIntegerRow 16 3 1 22229760,
    decodeIntegerRow 16 3 1 23059360,
    decodeIntegerRow 16 3 1 19988812,
    decodeIntegerRow 16 3 1 22234136,
    decodeIntegerRow 16 3 1 16759840,
    decodeIntegerRow 16 3 1 7168000]

def cols_left0 (r : LeftIndex 5 2 2) : List ℤ := cols_left0Data.getD (leftPosition 5 2 2 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 2 2) : (tripleIndices 2 4 2).map (fun j => (left0Middle5 2 2) j r) = cols_left0 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 78754883812,
    decodeIntegerRow 16 5 2 75903326612,
    decodeIntegerRow 16 5 2 15258039052,
    decodeIntegerRow 16 5 2 88497226564,
    decodeIntegerRow 16 5 2 88496914060,
    decodeIntegerRow 16 5 2 137329914052,
    decodeIntegerRow 16 5 2 75903314012,
    decodeIntegerRow 16 5 2 73833008812,
    decodeIntegerRow 16 5 2 75708001612,
    decodeIntegerRow 16 5 2 73872071812,
    decodeIntegerRow 16 5 2 64083164060,
    decodeIntegerRow 16 5 2 15259539052,
    decodeIntegerRow 16 5 2 15259601572,
    decodeIntegerRow 16 5 2 88505039060,
    decodeIntegerRow 16 5 2 73872068812,
    decodeIntegerRow 16 5 2 76879876612]

def cols_right2 (r : LeftIndex 5 2 2) : List ℤ := cols_right2Data.getD (leftPosition 5 2 2 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 2 2) : (tripleIndices 4 2 2).map (fun j => (right2Middle5 2 2) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms522.outerABC * HexagonAtoms522.assocABC = HexagonAtoms522.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product1_eq : HexagonAtoms522.assocBAC * HexagonAtoms522.innerABC = HexagonAtoms522.assocBAC :=
  Matrix.mul_one (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product2_eq : HexagonAtoms522.innerRightABC * HexagonAtoms522.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms522.inverseACB * right0Middle5 2 2 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms522.innerABC * right1Middle5 2 2 = right1Middle5 2 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product5_eq : HexagonAtoms522.assocBCA * left0Middle5 2 2 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms522.innerRightBAC * left1Middle5 2 2 = left1Middle5 2 2 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 2) (n := Fin 4 × Fin 2 × Fin 2) _

theorem product7_eq : HexagonAtoms522.assocBAC * right2Middle5 2 2 = rowColumnMul rows_assocBAC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBAC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn522
