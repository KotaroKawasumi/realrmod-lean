import RMod.BrundanEllis.StackingReferenceHexagonAtoms444
import RMod.BrundanEllis.StackingReferenceHexagonMiddle4
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn444
open Superfusion

theorem assocBAC_alias : HexagonAtoms444.assocBAC = HexagonAtoms444.assocABC :=
  HexagonAtoms444.assocBAC_eq.symm.trans HexagonAtoms444.assocABC_eq

theorem innerACB_alias : HexagonAtoms444.innerACB = HexagonAtoms444.innerABC :=
  HexagonAtoms444.innerACB_eq.symm.trans HexagonAtoms444.innerABC_eq

theorem assocBCA_alias : HexagonAtoms444.assocBCA = HexagonAtoms444.assocABC :=
  HexagonAtoms444.assocBCA_eq.symm.trans HexagonAtoms444.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms444.innerRightBAC = HexagonAtoms444.innerRightABC :=
  HexagonAtoms444.innerRightBAC_eq.symm.trans HexagonAtoms444.innerRightABC_eq

theorem assocCAB_alias : HexagonAtoms444.assocCAB = HexagonAtoms444.assocABC :=
  HexagonAtoms444.assocCAB_eq.symm.trans HexagonAtoms444.assocABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 7115162,
    decodeIntegerRow 16 3 1 16917622,
    decodeIntegerRow 16 3 1 23122066,
    decodeIntegerRow 16 3 1 22035874,
    decodeIntegerRow 16 3 1 16917454,
    decodeIntegerRow 16 3 1 35931074,
    decodeIntegerRow 16 3 1 22034362,
    decodeIntegerRow 16 3 1 19920298,
    decodeIntegerRow 16 3 1 23108926,
    decodeIntegerRow 16 3 1 20971534,
    decodeIntegerRow 16 3 1 35813462,
    decodeIntegerRow 16 3 1 16563322,
    decodeIntegerRow 16 3 1 20972938,
    decodeIntegerRow 16 3 1 19933402,
    decodeIntegerRow 16 3 1 16563166,
    decodeIntegerRow 16 3 1 7233746]

def rows_assocABC (r : RightIndex 4 4 4) : List ℤ := rows_assocABCData.getD (rightPosition 4 4 4 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 4 4 4) : (tripleIndices 4 1 4).map ((HexagonAtoms444.assocABC) r) = rows_assocABC r := by
  fin_cases r
  · exact rows_assocABC_eq_0_0_0
  · exact rows_assocABC_eq_0_0_1
  · exact rows_assocABC_eq_0_0_2
  · exact rows_assocABC_eq_0_0_3
  · exact rows_assocABC_eq_1_0_0
  · exact rows_assocABC_eq_1_0_1
  · exact rows_assocABC_eq_1_0_2
  · exact rows_assocABC_eq_1_0_3
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_0_2
  · exact rows_assocABC_eq_2_0_3
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_0_2
  · exact rows_assocABC_eq_3_0_3

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

def rows_innerRightABC (r : RightIndex 4 4 4) : List ℤ := rows_innerRightABCData.getD (rightPosition 4 4 4 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 4 4 4) : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerRightABC) r) = rows_innerRightABC r := by
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

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 19924672,
    decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 16917460,
    decodeIntegerRow 16 3 1 35931072,
    decodeIntegerRow 16 3 1 22034416,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 35813460,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 20972992,
    decodeIntegerRow 16 3 1 19933420,
    decodeIntegerRow 16 3 1 16563160,
    decodeIntegerRow 16 3 1 7233744]

def rows_inverseACB (r : LeftIndex 4 4 4) : List ℤ := rows_inverseACBData.getD (leftPosition 4 4 4 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map ((HexagonAtoms444.inverseACB) r) = rows_inverseACB r := by
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

private def rows_innerABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def rows_innerABC (r : LeftIndex 4 4 4) : List ℤ := rows_innerABCData.getD (leftPosition 4 4 4 r) []

private theorem rows_innerABC_eq_0_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_0 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = rows_innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_1 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = rows_innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_2 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = rows_innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_3 : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = rows_innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerABC_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map ((HexagonAtoms444.innerABC) r) = rows_innerABC r := by
  fin_cases r
  · exact rows_innerABC_eq_0_0_0
  · exact rows_innerABC_eq_0_0_1
  · exact rows_innerABC_eq_0_0_2
  · exact rows_innerABC_eq_0_0_3
  · exact rows_innerABC_eq_1_0_0
  · exact rows_innerABC_eq_1_0_1
  · exact rows_innerABC_eq_1_0_2
  · exact rows_innerABC_eq_1_0_3
  · exact rows_innerABC_eq_2_0_0
  · exact rows_innerABC_eq_2_0_1
  · exact rows_innerABC_eq_2_0_2
  · exact rows_innerABC_eq_2_0_3
  · exact rows_innerABC_eq_3_0_0
  · exact rows_innerABC_eq_3_0_1
  · exact rows_innerABC_eq_3_0_2
  · exact rows_innerABC_eq_3_0_3

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

def cols_innerABC (r : LeftIndex 4 4 4) : List ℤ := cols_innerABCData.getD (leftPosition 4 4 4 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.innerABC) j r) = cols_innerABC r := by
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

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 19924672,
    decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 16917460,
    decodeIntegerRow 16 3 1 35931072,
    decodeIntegerRow 16 3 1 22034416,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 35813460,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 20972992,
    decodeIntegerRow 16 3 1 19933420,
    decodeIntegerRow 16 3 1 16563160,
    decodeIntegerRow 16 3 1 7233744]

def cols_assocABC (r : LeftIndex 4 4 4) : List ℤ := cols_assocABCData.getD (leftPosition 4 4 4 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map (fun j => (HexagonAtoms444.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_0_2
  · exact cols_assocABC_eq_0_0_3
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_0_2
  · exact cols_assocABC_eq_1_0_3
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 7115162,
    decodeIntegerRow 16 3 1 16917622,
    decodeIntegerRow 16 3 1 23122066,
    decodeIntegerRow 16 3 1 22035874,
    decodeIntegerRow 16 3 1 26129266,
    decodeIntegerRow 16 3 1 7115646,
    decodeIntegerRow 16 3 1 21012358,
    decodeIntegerRow 16 3 1 23126422,
    decodeIntegerRow 16 3 1 19937794,
    decodeIntegerRow 16 3 1 22075186,
    decodeIntegerRow 16 3 1 7233258,
    decodeIntegerRow 16 3 1 26483398,
    decodeIntegerRow 16 3 1 22073782,
    decodeIntegerRow 16 3 1 23113318,
    decodeIntegerRow 16 3 1 26483554,
    decodeIntegerRow 16 3 1 35812974]

def cols_right0 (r : LeftIndex 4 4 4) : List ℤ := cols_right0Data.getD (leftPosition 4 4 4 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map (fun j => (right0Middle4 4 4) j r) = cols_right0 r := by
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

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 16 5 2 15239251560,
    decodeIntegerRow 16 5 2 64184571552,
    decodeIntegerRow 16 5 2 78735976512,
    decodeIntegerRow 16 5 2 76778351312,
    decodeIntegerRow 16 5 2 64184569072,
    decodeIntegerRow 16 5 2 137348626560,
    decodeIntegerRow 16 5 2 76778289312,
    decodeIntegerRow 16 5 2 73851601512,
    decodeIntegerRow 16 5 2 78734414112,
    decodeIntegerRow 16 5 2 75801726312,
    decodeIntegerRow 16 5 2 137309576560,
    decodeIntegerRow 16 5 2 63989259072,
    decodeIntegerRow 16 5 2 75801789312,
    decodeIntegerRow 16 5 2 73853164112,
    decodeIntegerRow 16 5 2 63989256552,
    decodeIntegerRow 16 5 2 15278326560]

def cols_right1 (r : LeftIndex 4 4 4) : List ℤ := cols_right1Data.getD (leftPosition 4 4 4 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right1 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map (fun j => (right1Middle4 4 4) j r) = cols_right1 r := by
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

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 19924672,
    decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 16917460,
    decodeIntegerRow 16 3 1 35931072,
    decodeIntegerRow 16 3 1 22034416,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 35813460,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 20972992,
    decodeIntegerRow 16 3 1 19933420,
    decodeIntegerRow 16 3 1 16563160,
    decodeIntegerRow 16 3 1 7233744]

def cols_left0 (r : LeftIndex 4 4 4) : List ℤ := cols_left0Data.getD (leftPosition 4 4 4 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map (fun j => (left0Middle4 4 4) j r) = cols_left0 r := by
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

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 19924672,
    decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 26129260,
    decodeIntegerRow 16 3 1 7115648,
    decodeIntegerRow 16 3 1 21012304,
    decodeIntegerRow 16 3 1 23126440,
    decodeIntegerRow 16 3 1 19937776,
    decodeIntegerRow 16 3 1 22075240,
    decodeIntegerRow 16 3 1 7233260,
    decodeIntegerRow 16 3 1 26483392,
    decodeIntegerRow 16 3 1 22073728,
    decodeIntegerRow 16 3 1 23113300,
    decodeIntegerRow 16 3 1 26483560,
    decodeIntegerRow 16 3 1 35812976]

def cols_left1 (r : LeftIndex 4 4 4) : List ℤ := cols_left1Data.getD (leftPosition 4 4 4 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_left1 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map (fun j => (left1Middle4 4 4) j r) = cols_left1 r := by
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

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 16 5 2 137348639060,
    decodeIntegerRow 16 5 2 88403319052,
    decodeIntegerRow 16 5 2 73851914012,
    decodeIntegerRow 16 5 2 75809538812,
    decodeIntegerRow 16 5 2 88403321572,
    decodeIntegerRow 16 5 2 15239264060,
    decodeIntegerRow 16 5 2 75809601812,
    decodeIntegerRow 16 5 2 78736289012,
    decodeIntegerRow 16 5 2 73853476612,
    decodeIntegerRow 16 5 2 76786163812,
    decodeIntegerRow 16 5 2 15278314060,
    decodeIntegerRow 16 5 2 88598631572,
    decodeIntegerRow 16 5 2 76786101812,
    decodeIntegerRow 16 5 2 78734726612,
    decodeIntegerRow 16 5 2 88598634052,
    decodeIntegerRow 16 5 2 137309564060]

def cols_right2 (r : LeftIndex 4 4 4) : List ℤ := cols_right2Data.getD (leftPosition 4 4 4 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 4 4 4) : (tripleIndices 4 1 4).map (fun j => (right2Middle4 4 4) j r) = cols_right2 r := by
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

theorem product0_eq : HexagonAtoms444.outerABC * HexagonAtoms444.assocABC = HexagonAtoms444.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 1 × Fin 4) (n := Fin 4 × Fin 1 × Fin 4) _

theorem product1_eq : HexagonAtoms444.assocABC * HexagonAtoms444.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms444.innerRightABC * HexagonAtoms444.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms444.inverseACB * right0Middle4 4 4 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms444.innerABC * right1Middle4 4 4 = rowColumnMul rows_innerABC cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerABC_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms444.assocABC * left0Middle4 4 4 = rowColumnMul rows_assocABC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms444.innerRightABC * left1Middle4 4 4 = rowColumnMul rows_innerRightABC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms444.assocABC * right2Middle4 4 4 = rowColumnMul rows_assocABC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn444
