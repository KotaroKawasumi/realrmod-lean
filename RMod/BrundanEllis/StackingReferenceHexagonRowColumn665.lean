import RMod.BrundanEllis.StackingReferenceHexagonAtoms665
import RMod.BrundanEllis.StackingReferenceHexagonMiddle6
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn665
open Superfusion

theorem assocBAC_alias : HexagonAtoms665.assocBAC = HexagonAtoms665.assocABC :=
  HexagonAtoms665.assocBAC_eq.symm.trans HexagonAtoms665.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms665.innerRightBAC = HexagonAtoms665.innerRightABC :=
  HexagonAtoms665.innerRightBAC_eq.symm.trans HexagonAtoms665.innerRightABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 16407716,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8717128,
    decodeIntegerRow 16 3 1 25934792,
    decodeIntegerRow 16 3 1 34224676,
    decodeIntegerRow 16 3 1 17116808,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 17431716,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 37531528,
    decodeIntegerRow 16 3 1 16403844,
    decodeIntegerRow 16 3 1 5646364,
    decodeIntegerRow 16 3 1 27036552]

def rows_assocABC (r : RightIndex 6 6 5) : List ℤ := rows_assocABCData.getD (rightPosition 6 6 5 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 6 6 5) : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_1_0
  · exact rows_assocABC_eq_0_1_1
  · exact rows_assocABC_eq_0_2_0
  · exact rows_assocABC_eq_0_2_1
  · exact rows_assocABC_eq_0_3_0
  · exact rows_assocABC_eq_0_3_1
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_1_0
  · exact rows_assocABC_eq_1_1_1
  · exact rows_assocABC_eq_1_2_0
  · exact rows_assocABC_eq_1_2_1
  · exact rows_assocABC_eq_1_3_0
  · exact rows_assocABC_eq_1_3_1

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 22072288,
    decodeIntegerRow 16 3 1 23111824,
    decodeIntegerRow 16 3 1 26128940,
    decodeIntegerRow 16 3 1 35931400,
    decodeIntegerRow 16 3 1 19921720,
    decodeIntegerRow 16 3 1 22032940,
    decodeIntegerRow 16 3 1 35813296,
    decodeIntegerRow 16 3 1 16563488,
    decodeIntegerRow 16 3 1 7115488,
    decodeIntegerRow 16 3 1 26129424,
    decodeIntegerRow 16 3 1 19936300,
    decodeIntegerRow 16 3 1 22076680,
    decodeIntegerRow 16 3 1 16563000,
    decodeIntegerRow 16 3 1 7233580,
    decodeIntegerRow 16 3 1 22037296,
    decodeIntegerRow 16 3 1 23123488]

def rows_inverseACB (r : LeftIndex 6 5 6) : List ℤ := rows_inverseACBData.getD (leftPosition 6 5 6 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 6 5 6) : (tripleIndices 2 4 2).map ((HexagonAtoms665.inverseACB) r) = rows_inverseACB r := by
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

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 16 3 1 20974432,
    decodeIntegerRow 16 3 1 19934896,
    decodeIntegerRow 16 3 1 16917780,
    decodeIntegerRow 16 3 1 7115320,
    decodeIntegerRow 16 3 1 23125000,
    decodeIntegerRow 16 3 1 21013780,
    decodeIntegerRow 16 3 1 7233424,
    decodeIntegerRow 16 3 1 26483232,
    decodeIntegerRow 16 3 1 35931232,
    decodeIntegerRow 16 3 1 16917296,
    decodeIntegerRow 16 3 1 23110420,
    decodeIntegerRow 16 3 1 20970040,
    decodeIntegerRow 16 3 1 26483720,
    decodeIntegerRow 16 3 1 35813140,
    decodeIntegerRow 16 3 1 21009424,
    decodeIntegerRow 16 3 1 19923232]

def rows_assocBCA (r : RightIndex 6 5 6) : List ℤ := rows_assocBCAData.getD (rightPosition 6 5 6 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocBCA ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 6 5 6) : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocBCA) r) = rows_assocBCA r := by
  fin_cases r
  · exact rows_assocBCA_eq_0_0_0
  · exact rows_assocBCA_eq_0_0_1
  · exact rows_assocBCA_eq_0_1_0
  · exact rows_assocBCA_eq_0_1_1
  · exact rows_assocBCA_eq_0_2_0
  · exact rows_assocBCA_eq_0_2_1
  · exact rows_assocBCA_eq_0_3_0
  · exact rows_assocBCA_eq_0_3_1
  · exact rows_assocBCA_eq_1_0_0
  · exact rows_assocBCA_eq_1_0_1
  · exact rows_assocBCA_eq_1_1_0
  · exact rows_assocBCA_eq_1_1_1
  · exact rows_assocBCA_eq_1_2_0
  · exact rows_assocBCA_eq_1_2_1
  · exact rows_assocBCA_eq_1_3_0
  · exact rows_assocBCA_eq_1_3_1

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 16 3 1 34211716,
    decodeIntegerRow 16 3 1 17073048,
    decodeIntegerRow 16 3 1 8702488,
    decodeIntegerRow 16 3 1 25576124,
    decodeIntegerRow 16 3 1 16363992,
    decodeIntegerRow 16 3 1 5528476,
    decodeIntegerRow 16 3 1 26992796,
    decodeIntegerRow 16 3 1 37414888,
    decodeIntegerRow 16 3 1 17076956,
    decodeIntegerRow 16 3 1 8833768,
    decodeIntegerRow 16 3 1 25579992,
    decodeIntegerRow 16 3 1 34342876,
    decodeIntegerRow 16 3 1 5526808,
    decodeIntegerRow 16 3 1 26677884,
    decodeIntegerRow 16 3 1 37413316,
    decodeIntegerRow 16 3 1 16049048]

def rows_assocCAB (r : RightIndex 5 6 6) : List ℤ := rows_assocCABData.getD (rightPosition 5 6 6 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_2_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_0 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_3_1 : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = rows_assocCAB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 5 6 6) : (tripleIndices 2 4 2).map ((HexagonAtoms665.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_2_0
  · exact rows_assocCAB_eq_0_2_1
  · exact rows_assocCAB_eq_0_3_0
  · exact rows_assocCAB_eq_0_3_1
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_2_0
  · exact rows_assocCAB_eq_1_2_1
  · exact rows_assocCAB_eq_1_3_0
  · exact rows_assocCAB_eq_1_3_1

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799]

def cols_innerABC (r : LeftIndex 6 6 5) : List ℤ := cols_innerABCData.getD (leftPosition 6 6 5 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 6 6 5) : (tripleIndices 2 4 2).map (fun j => (HexagonAtoms665.innerABC) j r) = cols_innerABC r := by
  fin_cases r
  · exact cols_innerABC_eq_0_0_0
  · exact cols_innerABC_eq_0_0_1
  · exact cols_innerABC_eq_0_1_0
  · exact cols_innerABC_eq_0_1_1
  · exact cols_innerABC_eq_0_2_0
  · exact cols_innerABC_eq_0_2_1
  · exact cols_innerABC_eq_0_3_0
  · exact cols_innerABC_eq_0_3_1
  · exact cols_innerABC_eq_1_0_0
  · exact cols_innerABC_eq_1_0_1
  · exact cols_innerABC_eq_1_1_0
  · exact cols_innerABC_eq_1_1_1
  · exact cols_innerABC_eq_1_2_0
  · exact cols_innerABC_eq_1_2_1
  · exact cols_innerABC_eq_1_3_0
  · exact cols_innerABC_eq_1_3_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 5528476,
    decodeIntegerRow 16 3 1 26682728,
    decodeIntegerRow 16 3 1 37414888,
    decodeIntegerRow 16 3 1 16053924,
    decodeIntegerRow 16 3 1 17073048,
    decodeIntegerRow 16 3 1 8835004,
    decodeIntegerRow 16 3 1 25576124,
    decodeIntegerRow 16 3 1 34344232,
    decodeIntegerRow 16 3 1 26997672,
    decodeIntegerRow 16 3 1 37413316,
    decodeIntegerRow 16 3 1 26677884,
    decodeIntegerRow 16 3 1 37519912,
    decodeIntegerRow 16 3 1 34342876,
    decodeIntegerRow 16 3 1 17466728,
    decodeIntegerRow 16 3 1 34212952,
    decodeIntegerRow 16 3 1 17076956]

def cols_right0 (r : LeftIndex 6 6 5) : List ℤ := cols_right0Data.getD (leftPosition 6 6 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 6 6 5) : (tripleIndices 2 4 2).map (fun j => (right0Middle6 6 5) j r) = cols_right0 r := by
  fin_cases r
  · exact cols_right0_eq_0_0_0
  · exact cols_right0_eq_0_0_1
  · exact cols_right0_eq_0_1_0
  · exact cols_right0_eq_0_1_1
  · exact cols_right0_eq_0_2_0
  · exact cols_right0_eq_0_2_1
  · exact cols_right0_eq_0_3_0
  · exact cols_right0_eq_0_3_1
  · exact cols_right0_eq_1_0_0
  · exact cols_right0_eq_1_0_1
  · exact cols_right0_eq_1_1_0
  · exact cols_right0_eq_1_1_1
  · exact cols_right0_eq_1_2_0
  · exact cols_right0_eq_1_2_1
  · exact cols_right0_eq_1_3_0
  · exact cols_right0_eq_1_3_1

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 5528476,
    decodeIntegerRow 16 3 1 26682728,
    decodeIntegerRow 16 3 1 37414888,
    decodeIntegerRow 16 3 1 16053924,
    decodeIntegerRow 16 3 1 17073048,
    decodeIntegerRow 16 3 1 8835004,
    decodeIntegerRow 16 3 1 25576124,
    decodeIntegerRow 16 3 1 34344232,
    decodeIntegerRow 16 3 1 26997672,
    decodeIntegerRow 16 3 1 37413316,
    decodeIntegerRow 16 3 1 26677884,
    decodeIntegerRow 16 3 1 37519912,
    decodeIntegerRow 16 3 1 34342876,
    decodeIntegerRow 16 3 1 17466728,
    decodeIntegerRow 16 3 1 34212952,
    decodeIntegerRow 16 3 1 17076956]

def cols_left0 (r : LeftIndex 6 6 5) : List ℤ := cols_left0Data.getD (leftPosition 6 6 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 6 6 5) : (tripleIndices 2 4 2).map (fun j => (left0Middle6 6 5) j r) = cols_left0 r := by
  fin_cases r
  · exact cols_left0_eq_0_0_0
  · exact cols_left0_eq_0_0_1
  · exact cols_left0_eq_0_1_0
  · exact cols_left0_eq_0_1_1
  · exact cols_left0_eq_0_2_0
  · exact cols_left0_eq_0_2_1
  · exact cols_left0_eq_0_3_0
  · exact cols_left0_eq_0_3_1
  · exact cols_left0_eq_1_0_0
  · exact cols_left0_eq_1_0_1
  · exact cols_left0_eq_1_1_0
  · exact cols_left0_eq_1_1_1
  · exact cols_left0_eq_1_2_0
  · exact cols_left0_eq_1_2_1
  · exact cols_left0_eq_1_3_0
  · exact cols_left0_eq_1_3_1

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 17720537552,
    decodeIntegerRow 16 5 2 88114407864,
    decodeIntegerRow 16 5 2 134908038072,
    decodeIntegerRow 16 5 2 64676907760,
    decodeIntegerRow 16 5 2 88895670264,
    decodeIntegerRow 16 5 2 139789225072,
    decodeIntegerRow 16 5 2 63505045360,
    decodeIntegerRow 16 5 2 12836100552,
    decodeIntegerRow 16 5 2 88114107760,
    decodeIntegerRow 16 5 2 134867412552,
    decodeIntegerRow 16 5 2 64676607864,
    decodeIntegerRow 16 5 2 17679913072,
    decodeIntegerRow 16 5 2 139789290552,
    decodeIntegerRow 16 5 2 63692545264,
    decodeIntegerRow 16 5 2 12836165072,
    decodeIntegerRow 16 5 2 89083170360]

def cols_right2 (r : LeftIndex 6 6 5) : List ℤ := cols_right2Data.getD (leftPosition 6 6 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 2), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 6 6 5) : (tripleIndices 2 4 2).map (fun j => (right2Middle6 6 5) j r) = cols_right2 r := by
  fin_cases r
  · exact cols_right2_eq_0_0_0
  · exact cols_right2_eq_0_0_1
  · exact cols_right2_eq_0_1_0
  · exact cols_right2_eq_0_1_1
  · exact cols_right2_eq_0_2_0
  · exact cols_right2_eq_0_2_1
  · exact cols_right2_eq_0_3_0
  · exact cols_right2_eq_0_3_1
  · exact cols_right2_eq_1_0_0
  · exact cols_right2_eq_1_0_1
  · exact cols_right2_eq_1_1_0
  · exact cols_right2_eq_1_1_1
  · exact cols_right2_eq_1_2_0
  · exact cols_right2_eq_1_2_1
  · exact cols_right2_eq_1_3_0
  · exact cols_right2_eq_1_3_1

theorem product0_eq : HexagonAtoms665.outerABC * HexagonAtoms665.assocABC = HexagonAtoms665.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms665.assocABC * HexagonAtoms665.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms665.innerRightABC * HexagonAtoms665.assocABC = HexagonAtoms665.assocABC :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product3_eq : HexagonAtoms665.inverseACB * right0Middle6 6 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms665.innerACB * right1Middle6 6 5 = right1Middle6 6 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product5_eq : HexagonAtoms665.assocBCA * left0Middle6 6 5 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms665.innerRightABC * left1Middle6 6 5 = left1Middle6 6 5 :=
  Matrix.one_mul (m := Fin 2 × Fin 4 × Fin 2) (n := Fin 2 × Fin 4 × Fin 2) _

theorem product7_eq : HexagonAtoms665.assocCAB * right2Middle6 6 5 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn665
