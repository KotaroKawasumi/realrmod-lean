import RMod.BrundanEllis.StackingReferenceHexagonAtoms555
import RMod.BrundanEllis.StackingReferenceHexagonMiddle5
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn555
open Superfusion

theorem assocBAC_alias : HexagonAtoms555.assocBAC = HexagonAtoms555.assocABC :=
  HexagonAtoms555.assocBAC_eq.symm.trans HexagonAtoms555.assocABC_eq

theorem innerACB_alias : HexagonAtoms555.innerACB = HexagonAtoms555.innerABC :=
  HexagonAtoms555.innerACB_eq.symm.trans HexagonAtoms555.innerABC_eq

theorem assocBCA_alias : HexagonAtoms555.assocBCA = HexagonAtoms555.assocABC :=
  HexagonAtoms555.assocBCA_eq.symm.trans HexagonAtoms555.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms555.innerRightBAC = HexagonAtoms555.innerRightABC :=
  HexagonAtoms555.innerRightBAC_eq.symm.trans HexagonAtoms555.innerRightABC_eq

theorem assocCAB_alias : HexagonAtoms555.assocCAB = HexagonAtoms555.assocABC :=
  HexagonAtoms555.assocCAB_eq.symm.trans HexagonAtoms555.assocABC_eq

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 706186115764736,
    decodeIntegerRow 32 3 1 242946584532736,
    decodeIntegerRow 32 3 1 750310238914320,
    decodeIntegerRow 32 3 1 379831551308560,
    decodeIntegerRow 32 3 1 1477916717583400,
    decodeIntegerRow 32 3 1 1116336303503960,
    decodeIntegerRow 32 3 1 1615554829080928,
    decodeIntegerRow 32 3 1 1163724056615712,
    decodeIntegerRow 32 3 1 1102782300446480,
    decodeIntegerRow 32 3 1 1473398716564240,
    decodeIntegerRow 32 3 1 1146776192679936,
    decodeIntegerRow 32 3 1 1609905541102336,
    decodeIntegerRow 32 3 1 1615721497796512,
    decodeIntegerRow 32 3 1 1163777753519328,
    decodeIntegerRow 32 3 1 1477708381688920,
    decodeIntegerRow 32 3 1 1116269182374440,
    decodeIntegerRow 32 3 1 242946593352280,
    decodeIntegerRow 32 3 1 706186141383720,
    decodeIntegerRow 32 3 1 1473188648564512,
    decodeIntegerRow 32 3 1 1102709981951328,
    decodeIntegerRow 32 3 1 1116336335263104,
    decodeIntegerRow 32 3 1 1477916727819904,
    decodeIntegerRow 32 3 1 689296157635440,
    decodeIntegerRow 32 3 1 237465367957360,
    decodeIntegerRow 32 3 1 1473398705540512,
    decodeIntegerRow 32 3 1 1102782268424928,
    decodeIntegerRow 32 3 1 243114638933080,
    decodeIntegerRow 32 3 1 706243970562600,
    decodeIntegerRow 32 3 1 1163777778928400,
    decodeIntegerRow 32 3 1 1615721505986320,
    decodeIntegerRow 32 3 1 736751038228736,
    decodeIntegerRow 32 3 1 375311817396736]

def rows_assocABC (r : RightIndex 5 5 5) : List ℤ := rows_assocABCData.getD (rightPosition 5 5 5 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_assocABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 5 5 5) : (tripleIndices 4 4 2).map ((HexagonAtoms555.assocABC) r) = rows_assocABC r := by
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
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_1_0
  · exact rows_assocABC_eq_2_1_1
  · exact rows_assocABC_eq_2_2_0
  · exact rows_assocABC_eq_2_2_1
  · exact rows_assocABC_eq_2_3_0
  · exact rows_assocABC_eq_2_3_1
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_1_0
  · exact rows_assocABC_eq_3_1_1
  · exact rows_assocABC_eq_3_2_0
  · exact rows_assocABC_eq_3_2_1
  · exact rows_assocABC_eq_3_3_0
  · exact rows_assocABC_eq_3_3_1

private def rows_innerRightABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 924250222353100,
    decodeIntegerRow 32 3 1 919730478207460,
    decodeIntegerRow 32 3 1 929334041164624,
    decodeIntegerRow 32 3 1 934981934642032,
    decodeIntegerRow 32 3 1 1155305913198260,
    decodeIntegerRow 32 3 1 1612897550742940,
    decodeIntegerRow 32 3 1 1109489566287216,
    decodeIntegerRow 32 3 1 1475448510009808,
    decodeIntegerRow 32 3 1 923686139182540,
    decodeIntegerRow 32 3 1 918038228695780,
    decodeIntegerRow 32 3 1 924250232980624,
    decodeIntegerRow 32 3 1 919730510090032,
    decodeIntegerRow 32 3 1 1109489566155980,
    decodeIntegerRow 32 3 1 1475448509616100,
    decodeIntegerRow 32 3 1 697714275548624,
    decodeIntegerRow 32 3 1 240122637794032,
    decodeIntegerRow 32 3 1 1109559301975220,
    decodeIntegerRow 32 3 1 1475657717073820,
    decodeIntegerRow 32 3 1 697770064204016,
    decodeIntegerRow 32 3 1 240290003760208,
    decodeIntegerRow 32 3 1 929334729913780,
    decodeIntegerRow 32 3 1 934984000889500,
    decodeIntegerRow 32 3 1 928769105565616,
    decodeIntegerRow 32 3 1 933287127845008,
    decodeIntegerRow 32 3 1 697770064099020,
    decodeIntegerRow 32 3 1 240290003445220,
    decodeIntegerRow 32 3 1 743460887007824,
    decodeIntegerRow 32 3 1 377362472171632,
    decodeIntegerRow 32 3 1 924251093916340,
    decodeIntegerRow 32 3 1 919733092897180,
    decodeIntegerRow 32 3 1 929334738415216,
    decodeIntegerRow 32 3 1 934984026393808]

def rows_innerRightABC (r : RightIndex 5 5 5) : List ℤ := rows_innerRightABCData.getD (rightPosition 5 5 5 r) []

private theorem rows_innerRightABC_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerRightABC_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerRightABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerRightABC_data (r : RightIndex 5 5 5) : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerRightABC) r) = rows_innerRightABC r := by
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
  · exact rows_innerRightABC_eq_2_0_0
  · exact rows_innerRightABC_eq_2_0_1
  · exact rows_innerRightABC_eq_2_1_0
  · exact rows_innerRightABC_eq_2_1_1
  · exact rows_innerRightABC_eq_2_2_0
  · exact rows_innerRightABC_eq_2_2_1
  · exact rows_innerRightABC_eq_2_3_0
  · exact rows_innerRightABC_eq_2_3_1
  · exact rows_innerRightABC_eq_3_0_0
  · exact rows_innerRightABC_eq_3_0_1
  · exact rows_innerRightABC_eq_3_1_0
  · exact rows_innerRightABC_eq_3_1_1
  · exact rows_innerRightABC_eq_3_2_0
  · exact rows_innerRightABC_eq_3_2_1
  · exact rows_innerRightABC_eq_3_3_0
  · exact rows_innerRightABC_eq_3_3_1

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768986335604,
    decodeIntegerRow 32 3 1 1609884542804092,
    decodeIntegerRow 32 3 1 736690568745524,
    decodeIntegerRow 32 3 1 375124295251132,
    decodeIntegerRow 32 3 1 1615533994783108,
    decodeIntegerRow 32 3 1 1163717341432716,
    decodeIntegerRow 32 3 1 379642479480892,
    decodeIntegerRow 32 3 1 750245120385204,
    decodeIntegerRow 32 3 1 750302975183108,
    decodeIntegerRow 32 3 1 379810533881356,
    decodeIntegerRow 32 3 1 689235694530492,
    decodeIntegerRow 32 3 1 237277847937844,
    decodeIntegerRow 32 3 1 1477729216695436,
    decodeIntegerRow 32 3 1 1116275897793668,
    decodeIntegerRow 32 3 1 1610094610803916,
    decodeIntegerRow 32 3 1 1146841304830788,
    decodeIntegerRow 32 3 1 375290983177324,
    decodeIntegerRow 32 3 1 736744323071012,
    decodeIntegerRow 32 3 1 242925586237396,
    decodeIntegerRow 32 3 1 706178909429148,
    decodeIntegerRow 32 3 1 1102717181918372,
    decodeIntegerRow 32 3 1 1473209644737004,
    decodeIntegerRow 32 3 1 1163784468703332,
    decodeIntegerRow 32 3 1 1615742332094764,
    decodeIntegerRow 32 3 1 1615533985966372,
    decodeIntegerRow 32 3 1 1163717315822444,
    decodeIntegerRow 32 3 1 379642489717732,
    decodeIntegerRow 32 3 1 750245152145324,
    decodeIntegerRow 32 3 1 1146768960935316,
    decodeIntegerRow 32 3 1 1609884534617308,
    decodeIntegerRow 32 3 1 736690600768044,
    decodeIntegerRow 32 3 1 375124306275172]

def rows_inverseACB (r : LeftIndex 5 5 5) : List ℤ := rows_inverseACBData.getD (leftPosition 5 5 5 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_inverseACB ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map ((HexagonAtoms555.inverseACB) r) = rows_inverseACB r := by
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
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_2_0
  · exact rows_inverseACB_eq_2_2_1
  · exact rows_inverseACB_eq_2_3_0
  · exact rows_inverseACB_eq_2_3_1
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_2_0
  · exact rows_inverseACB_eq_3_2_1
  · exact rows_inverseACB_eq_3_3_0
  · exact rows_inverseACB_eq_3_3_1

private def rows_innerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 924250222353100,
    decodeIntegerRow 32 3 1 919730478207460,
    decodeIntegerRow 32 3 1 929334041164624,
    decodeIntegerRow 32 3 1 934981934642032,
    decodeIntegerRow 32 3 1 1155305913198260,
    decodeIntegerRow 32 3 1 1612897550742940,
    decodeIntegerRow 32 3 1 1109489566287216,
    decodeIntegerRow 32 3 1 1475448510009808,
    decodeIntegerRow 32 3 1 923686139182540,
    decodeIntegerRow 32 3 1 918038228695780,
    decodeIntegerRow 32 3 1 924250232980624,
    decodeIntegerRow 32 3 1 919730510090032,
    decodeIntegerRow 32 3 1 1109489566155980,
    decodeIntegerRow 32 3 1 1475448509616100,
    decodeIntegerRow 32 3 1 697714275548624,
    decodeIntegerRow 32 3 1 240122637794032,
    decodeIntegerRow 32 3 1 1109559301975220,
    decodeIntegerRow 32 3 1 1475657717073820,
    decodeIntegerRow 32 3 1 697770064204016,
    decodeIntegerRow 32 3 1 240290003760208,
    decodeIntegerRow 32 3 1 929334729913780,
    decodeIntegerRow 32 3 1 934984000889500,
    decodeIntegerRow 32 3 1 928769105565616,
    decodeIntegerRow 32 3 1 933287127845008,
    decodeIntegerRow 32 3 1 697770064099020,
    decodeIntegerRow 32 3 1 240290003445220,
    decodeIntegerRow 32 3 1 743460887007824,
    decodeIntegerRow 32 3 1 377362472171632,
    decodeIntegerRow 32 3 1 924251093916340,
    decodeIntegerRow 32 3 1 919733092897180,
    decodeIntegerRow 32 3 1 929334738415216,
    decodeIntegerRow 32 3 1 934984026393808]

def rows_innerABC (r : LeftIndex 5 5 5) : List ℤ := rows_innerABCData.getD (leftPosition 5 5 5 r) []

private theorem rows_innerABC_eq_0_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_0_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_1_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_2_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_0_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_1_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_1_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_2_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_2_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_3_0 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = rows_innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_innerABC_eq_3_3_1 : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = rows_innerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_innerABC_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map ((HexagonAtoms555.innerABC) r) = rows_innerABC r := by
  fin_cases r
  · exact rows_innerABC_eq_0_0_0
  · exact rows_innerABC_eq_0_0_1
  · exact rows_innerABC_eq_0_1_0
  · exact rows_innerABC_eq_0_1_1
  · exact rows_innerABC_eq_0_2_0
  · exact rows_innerABC_eq_0_2_1
  · exact rows_innerABC_eq_0_3_0
  · exact rows_innerABC_eq_0_3_1
  · exact rows_innerABC_eq_1_0_0
  · exact rows_innerABC_eq_1_0_1
  · exact rows_innerABC_eq_1_1_0
  · exact rows_innerABC_eq_1_1_1
  · exact rows_innerABC_eq_1_2_0
  · exact rows_innerABC_eq_1_2_1
  · exact rows_innerABC_eq_1_3_0
  · exact rows_innerABC_eq_1_3_1
  · exact rows_innerABC_eq_2_0_0
  · exact rows_innerABC_eq_2_0_1
  · exact rows_innerABC_eq_2_1_0
  · exact rows_innerABC_eq_2_1_1
  · exact rows_innerABC_eq_2_2_0
  · exact rows_innerABC_eq_2_2_1
  · exact rows_innerABC_eq_2_3_0
  · exact rows_innerABC_eq_2_3_1
  · exact rows_innerABC_eq_3_0_0
  · exact rows_innerABC_eq_3_0_1
  · exact rows_innerABC_eq_3_1_0
  · exact rows_innerABC_eq_3_1_1
  · exact rows_innerABC_eq_3_2_0
  · exact rows_innerABC_eq_3_2_1
  · exact rows_innerABC_eq_3_3_0
  · exact rows_innerABC_eq_3_3_1

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 928769966498740,
    decodeIntegerRow 32 3 1 933289710644380,
    decodeIntegerRow 32 3 1 923686147687216,
    decodeIntegerRow 32 3 1 918038254209808,
    decodeIntegerRow 32 3 1 697714275653580,
    decodeIntegerRow 32 3 1 240122638108900,
    decodeIntegerRow 32 3 1 743530622564624,
    decodeIntegerRow 32 3 1 377571678842032,
    decodeIntegerRow 32 3 1 929334049669300,
    decodeIntegerRow 32 3 1 934981960156060,
    decodeIntegerRow 32 3 1 928769955871216,
    decodeIntegerRow 32 3 1 933289678761808,
    decodeIntegerRow 32 3 1 743530622695860,
    decodeIntegerRow 32 3 1 377571679235740,
    decodeIntegerRow 32 3 1 1155305913303216,
    decodeIntegerRow 32 3 1 1612897551057808,
    decodeIntegerRow 32 3 1 743460886876620,
    decodeIntegerRow 32 3 1 377362471778020,
    decodeIntegerRow 32 3 1 1155250124647824,
    decodeIntegerRow 32 3 1 1612730185091632,
    decodeIntegerRow 32 3 1 923685458938060,
    decodeIntegerRow 32 3 1 918036187962340,
    decodeIntegerRow 32 3 1 924251083286224,
    decodeIntegerRow 32 3 1 919733061006832,
    decodeIntegerRow 32 3 1 1155250124752820,
    decodeIntegerRow 32 3 1 1612730185406620,
    decodeIntegerRow 32 3 1 1109559301844016,
    decodeIntegerRow 32 3 1 1475657716680208,
    decodeIntegerRow 32 3 1 928769094935500,
    decodeIntegerRow 32 3 1 933287095954660,
    decodeIntegerRow 32 3 1 923685450436624,
    decodeIntegerRow 32 3 1 918036162458032]

def cols_innerABC (r : LeftIndex 5 5 5) : List ℤ := cols_innerABCData.getD (leftPosition 5 5 5 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_innerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.innerABC) j r) = cols_innerABC r := by
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
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_1_0
  · exact cols_innerABC_eq_2_1_1
  · exact cols_innerABC_eq_2_2_0
  · exact cols_innerABC_eq_2_2_1
  · exact cols_innerABC_eq_2_3_0
  · exact cols_innerABC_eq_2_3_1
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_1_0
  · exact cols_innerABC_eq_3_1_1
  · exact cols_innerABC_eq_3_2_0
  · exact cols_innerABC_eq_3_2_1
  · exact cols_innerABC_eq_3_3_0
  · exact cols_innerABC_eq_3_3_1

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768986335604,
    decodeIntegerRow 32 3 1 1609884542804092,
    decodeIntegerRow 32 3 1 736690568745524,
    decodeIntegerRow 32 3 1 375124295251132,
    decodeIntegerRow 32 3 1 1615533994783108,
    decodeIntegerRow 32 3 1 1163717341432716,
    decodeIntegerRow 32 3 1 379642479480892,
    decodeIntegerRow 32 3 1 750245120385204,
    decodeIntegerRow 32 3 1 750302975183108,
    decodeIntegerRow 32 3 1 379810533881356,
    decodeIntegerRow 32 3 1 689235694530492,
    decodeIntegerRow 32 3 1 237277847937844,
    decodeIntegerRow 32 3 1 1477729216695436,
    decodeIntegerRow 32 3 1 1116275897793668,
    decodeIntegerRow 32 3 1 1610094610803916,
    decodeIntegerRow 32 3 1 1146841304830788,
    decodeIntegerRow 32 3 1 375290983177324,
    decodeIntegerRow 32 3 1 736744323071012,
    decodeIntegerRow 32 3 1 242925586237396,
    decodeIntegerRow 32 3 1 706178909429148,
    decodeIntegerRow 32 3 1 1102717181918372,
    decodeIntegerRow 32 3 1 1473209644737004,
    decodeIntegerRow 32 3 1 1163784468703332,
    decodeIntegerRow 32 3 1 1615742332094764,
    decodeIntegerRow 32 3 1 1615533985966372,
    decodeIntegerRow 32 3 1 1163717315822444,
    decodeIntegerRow 32 3 1 379642489717732,
    decodeIntegerRow 32 3 1 750245152145324,
    decodeIntegerRow 32 3 1 1146768960935316,
    decodeIntegerRow 32 3 1 1609884534617308,
    decodeIntegerRow 32 3 1 736690600768044,
    decodeIntegerRow 32 3 1 375124306275172]

def cols_assocABC (r : LeftIndex 5 5 5) : List ℤ := cols_assocABCData.getD (leftPosition 5 5 5 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_assocABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map (fun j => (HexagonAtoms555.assocABC) j r) = cols_assocABC r := by
  fin_cases r
  · exact cols_assocABC_eq_0_0_0
  · exact cols_assocABC_eq_0_0_1
  · exact cols_assocABC_eq_0_1_0
  · exact cols_assocABC_eq_0_1_1
  · exact cols_assocABC_eq_0_2_0
  · exact cols_assocABC_eq_0_2_1
  · exact cols_assocABC_eq_0_3_0
  · exact cols_assocABC_eq_0_3_1
  · exact cols_assocABC_eq_1_0_0
  · exact cols_assocABC_eq_1_0_1
  · exact cols_assocABC_eq_1_1_0
  · exact cols_assocABC_eq_1_1_1
  · exact cols_assocABC_eq_1_2_0
  · exact cols_assocABC_eq_1_2_1
  · exact cols_assocABC_eq_1_3_0
  · exact cols_assocABC_eq_1_3_1
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_2_2_0
  · exact cols_assocABC_eq_2_2_1
  · exact cols_assocABC_eq_2_3_0
  · exact cols_assocABC_eq_2_3_1
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1
  · exact cols_assocABC_eq_3_2_0
  · exact cols_assocABC_eq_3_2_1
  · exact cols_assocABC_eq_3_3_0
  · exact cols_assocABC_eq_3_3_1

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 9 4 1698027239246551835870438833216,
    decodeIntegerRow 32 9 4 1714981118508124901893323062464,
    decodeIntegerRow 32 9 4 3242923253536507462171442271424,
    decodeIntegerRow 32 9 4 1886403667716020795079185032256,
    decodeIntegerRow 32 9 4 1886403667716019147949822165040,
    decodeIntegerRow 32 9 4 3242923253536507279154007519280,
    decodeIntegerRow 32 9 4 1714981118508124881530501688880,
    decodeIntegerRow 32 9 4 1698027239246551833359954017840,
    decodeIntegerRow 32 9 4 1698027240123104503494428931136,
    decodeIntegerRow 32 9 4 1714981118616193018944341527744,
    decodeIntegerRow 32 9 4 190760495852485424122326239296,
    decodeIntegerRow 32 9 4 1547280144698192701785577992384,
    decodeIntegerRow 32 9 4 1886403675594321430001710491600,
    decodeIntegerRow 32 9 4 3242923324440027243552966105040,
    decodeIntegerRow 32 9 4 1718702701676319445350687131440,
    decodeIntegerRow 32 9 4 1735656580169407978652935436080,
    decodeIntegerRow 32 9 4 1719167899583150579597488465360,
    decodeIntegerRow 32 9 4 1735708268825722549372751369680,
    decodeIntegerRow 32 9 4 1886409418778089547368478947280,
    decodeIntegerRow 32 9 4 3242923962571557034368434833360,
    decodeIntegerRow 32 9 4 190759857720955633300658783296,
    decodeIntegerRow 32 9 4 1547274401514424584418120789184,
    decodeIntegerRow 32 9 4 1697975551466789933276709962944,
    decodeIntegerRow 32 9 4 1714515920709361884753328745536,
    decodeIntegerRow 32 9 4 1719167899669605109835592310480,
    decodeIntegerRow 32 9 4 1735708269699873707350862065360,
    decodeIntegerRow 32 9 4 1547274409392458384433375055920,
    decodeIntegerRow 32 9 4 190759928624445766359152484400,
    decodeIntegerRow 32 9 4 190759928624445583347916460224,
    decodeIntegerRow 32 9 4 1547274409392456737304700936256,
    decodeIntegerRow 32 9 4 1735708269699873705342474192064,
    decodeIntegerRow 32 9 4 1719167899669605089528559486016]

def cols_right0 (r : LeftIndex 5 5 5) : List ℤ := cols_right0Data.getD (leftPosition 5 5 5 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right0 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map (fun j => (right0Middle5 5 5) j r) = cols_right0 r := by
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
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_2_0
  · exact cols_right0_eq_2_2_1
  · exact cols_right0_eq_2_3_0
  · exact cols_right0_eq_2_3_1
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_2_0
  · exact cols_right0_eq_3_2_1
  · exact cols_right0_eq_3_3_0
  · exact cols_right0_eq_3_3_1

private def cols_right1Data : List (List ℤ) := [decodeIntegerRow 32 65 32 5154629049087417059395383020731611442588081393826285157312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020682394237766840281326293810112,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380643429703305591918947392,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732392292472264546091918945344,
    decodeIntegerRow 32 65 32 5154647530023470648258058559241972865862636723709106445312,
    decodeIntegerRow 32 65 32 5155830309930900335469306748073451153697157348709106445312,
    decodeIntegerRow 32 65 32 5076547094261004114591232817704471663444389848709106445312,
    decodeIntegerRow 32 65 32 79301985370575647067635004708705562594749223709106445312,
    decodeIntegerRow 32 65 32 5153427788243933783321459286893100695075178588943481445312,
    decodeIntegerRow 32 65 32 5154610568151363470532707059839198243422298588943481445312,
    decodeIntegerRow 32 65 32 10229956112804258471723158491689393240455009233474731445312,
    decodeIntegerRow 32 65 32 5232711003913830004201317794427251473873009233474731445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020782366685059986291091918810112,
    decodeIntegerRow 32 65 32 5154629049087417059395383020733149480238745178591910157312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732368630354562026326293945344,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380279397123266826293947392,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380461413423482880248245312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380461414076067420490165312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380461370332350635001445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380458613162668112889445312,
    decodeIntegerRow 32 65 32 5154629053461587179731215108891401821935874223709106445312,
    decodeIntegerRow 32 65 32 5154629333409509946487872171171016875617514848709106445312,
    decodeIntegerRow 32 65 32 5154629049086381752858025427338733355765952348709106445312,
    decodeIntegerRow 32 65 32 5154629049020121889481278289572513328534311723709106445312,
    decodeIntegerRow 32 65 32 5154629333409510436575591585669171349093009233474731445312,
    decodeIntegerRow 32 65 32 5154629053461619035432977051271442597843009233474731445312,
    decodeIntegerRow 32 65 32 5154629049020121889365281196219969386647098588943481445312,
    decodeIntegerRow 32 65 32 5154629049086381745318214359423377133097098588943481445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380461414076067419347725312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380461413423482805989645312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380458613162672939698445312,
    decodeIntegerRow 32 65 32 5154629049087417059395383020732380461370332664377586445312]

def cols_right1 (r : LeftIndex 5 5 5) : List ℤ := cols_right1Data.getD (leftPosition 5 5 5 r) []

private theorem cols_right1_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right1 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right1_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right1 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right1_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map (fun j => (right1Middle5 5 5) j r) = cols_right1 r := by
  fin_cases r
  · exact cols_right1_eq_0_0_0
  · exact cols_right1_eq_0_0_1
  · exact cols_right1_eq_0_1_0
  · exact cols_right1_eq_0_1_1
  · exact cols_right1_eq_0_2_0
  · exact cols_right1_eq_0_2_1
  · exact cols_right1_eq_0_3_0
  · exact cols_right1_eq_0_3_1
  · exact cols_right1_eq_1_0_0
  · exact cols_right1_eq_1_0_1
  · exact cols_right1_eq_1_1_0
  · exact cols_right1_eq_1_1_1
  · exact cols_right1_eq_1_2_0
  · exact cols_right1_eq_1_2_1
  · exact cols_right1_eq_1_3_0
  · exact cols_right1_eq_1_3_1
  · exact cols_right1_eq_2_0_0
  · exact cols_right1_eq_2_0_1
  · exact cols_right1_eq_2_1_0
  · exact cols_right1_eq_2_1_1
  · exact cols_right1_eq_2_2_0
  · exact cols_right1_eq_2_2_1
  · exact cols_right1_eq_2_3_0
  · exact cols_right1_eq_2_3_1
  · exact cols_right1_eq_3_0_0
  · exact cols_right1_eq_3_0_1
  · exact cols_right1_eq_3_1_0
  · exact cols_right1_eq_3_1_1
  · exact cols_right1_eq_3_2_0
  · exact cols_right1_eq_3_2_1
  · exact cols_right1_eq_3_3_0
  · exact cols_right1_eq_3_3_1

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768986335604,
    decodeIntegerRow 32 3 1 1609884542804092,
    decodeIntegerRow 32 3 1 736690568745524,
    decodeIntegerRow 32 3 1 375124295251132,
    decodeIntegerRow 32 3 1 1615533994783108,
    decodeIntegerRow 32 3 1 1163717341432716,
    decodeIntegerRow 32 3 1 379642479480892,
    decodeIntegerRow 32 3 1 750245120385204,
    decodeIntegerRow 32 3 1 750302975183108,
    decodeIntegerRow 32 3 1 379810533881356,
    decodeIntegerRow 32 3 1 689235694530492,
    decodeIntegerRow 32 3 1 237277847937844,
    decodeIntegerRow 32 3 1 1477729216695436,
    decodeIntegerRow 32 3 1 1116275897793668,
    decodeIntegerRow 32 3 1 1610094610803916,
    decodeIntegerRow 32 3 1 1146841304830788,
    decodeIntegerRow 32 3 1 375290983177324,
    decodeIntegerRow 32 3 1 736744323071012,
    decodeIntegerRow 32 3 1 242925586237396,
    decodeIntegerRow 32 3 1 706178909429148,
    decodeIntegerRow 32 3 1 1102717181918372,
    decodeIntegerRow 32 3 1 1473209644737004,
    decodeIntegerRow 32 3 1 1163784468703332,
    decodeIntegerRow 32 3 1 1615742332094764,
    decodeIntegerRow 32 3 1 1615533985966372,
    decodeIntegerRow 32 3 1 1163717315822444,
    decodeIntegerRow 32 3 1 379642489717732,
    decodeIntegerRow 32 3 1 750245152145324,
    decodeIntegerRow 32 3 1 1146768960935316,
    decodeIntegerRow 32 3 1 1609884534617308,
    decodeIntegerRow 32 3 1 736690600768044,
    decodeIntegerRow 32 3 1 375124306275172]

def cols_left0 (r : LeftIndex 5 5 5) : List ℤ := cols_left0Data.getD (leftPosition 5 5 5 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left0 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left0 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map (fun j => (left0Middle5 5 5) j r) = cols_left0 r := by
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
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_2_0
  · exact cols_left0_eq_2_2_1
  · exact cols_left0_eq_2_3_0
  · exact cols_left0_eq_2_3_1
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_2_0
  · exact cols_left0_eq_3_2_1
  · exact cols_left0_eq_3_3_0
  · exact cols_left0_eq_3_3_1

private def cols_left1Data : List (List ℤ) := [decodeIntegerRow 32 17 8 1183955797380233622923400171272950870416,
    decodeIntegerRow 32 17 8 1183955797380233622944952533072554152336,
    decodeIntegerRow 32 17 8 1183955797380233622922048487682577785456,
    decodeIntegerRow 32 17 8 1183955797380233622921973912036212376176,
    decodeIntegerRow 32 17 8 1183728988640418687932873402892241232768,
    decodeIntegerRow 32 17 8 1180100048803379615990611389064025997952,
    decodeIntegerRow 32 17 8 1249503523186749834794999675680214597248,
    decodeIntegerRow 32 17 8 2298267136091041626108721672034417459072,
    decodeIntegerRow 32 17 8 1187811545957087630632073978267595145104,
    decodeIntegerRow 32 17 8 1184182606120048571147077084610098241424,
    decodeIntegerRow 32 17 8 69644458669425394726033392202933932144,
    decodeIntegerRow 32 17 8 1118408071573713585890135659219539095664,
    decodeIntegerRow 32 17 8 1183955797380233622899153764248397099648,
    decodeIntegerRow 32 17 8 1183955797380233622920706126048000455552,
    decodeIntegerRow 32 17 8 1183955797380233622922132385284738871168,
    decodeIntegerRow 32 17 8 1183955797380233622922057809638373461632,
    decodeIntegerRow 32 17 8 1183955797380233622922053148604658205296,
    decodeIntegerRow 32 17 8 1183955797380233622922053147711771943536,
    decodeIntegerRow 32 17 8 1183955797380233622922053164791709536656,
    decodeIntegerRow 32 17 8 1183955797380233622922053422835839185296,
    decodeIntegerRow 32 17 8 1183955012734646094746205803299429365632,
    decodeIntegerRow 32 17 8 1183942455699052776427922228046448801408,
    decodeIntegerRow 32 17 8 1183955800095270257967644315945461942912,
    decodeIntegerRow 32 17 8 1183955843545220407858018999596856339328,
    decodeIntegerRow 32 17 8 1183942455680259770403583852702863798384,
    decodeIntegerRow 32 17 8 1183955012415164992332453422458484314224,
    decodeIntegerRow 32 17 8 1183955843545285435560525360757214764944,
    decodeIntegerRow 32 17 8 1183955800096375728910252455671555178384,
    decodeIntegerRow 32 17 8 1183955797380233622922053147711773279872,
    decodeIntegerRow 32 17 8 1183955797380233622922053148604680923008,
    decodeIntegerRow 32 17 8 1183955797380233622922053422835452984192,
    decodeIntegerRow 32 17 8 1183955797380233622922053164785144117888]

def cols_left1 (r : LeftIndex 5 5 5) : List ℤ := cols_left1Data.getD (leftPosition 5 5 5 r) []

private theorem cols_left1_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_left1 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left1_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_left1 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left1_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map (fun j => (left1Middle5 5 5) j r) = cols_left1 r := by
  fin_cases r
  · exact cols_left1_eq_0_0_0
  · exact cols_left1_eq_0_0_1
  · exact cols_left1_eq_0_1_0
  · exact cols_left1_eq_0_1_1
  · exact cols_left1_eq_0_2_0
  · exact cols_left1_eq_0_2_1
  · exact cols_left1_eq_0_3_0
  · exact cols_left1_eq_0_3_1
  · exact cols_left1_eq_1_0_0
  · exact cols_left1_eq_1_0_1
  · exact cols_left1_eq_1_1_0
  · exact cols_left1_eq_1_1_1
  · exact cols_left1_eq_1_2_0
  · exact cols_left1_eq_1_2_1
  · exact cols_left1_eq_1_3_0
  · exact cols_left1_eq_1_3_1
  · exact cols_left1_eq_2_0_0
  · exact cols_left1_eq_2_0_1
  · exact cols_left1_eq_2_1_0
  · exact cols_left1_eq_2_1_1
  · exact cols_left1_eq_2_2_0
  · exact cols_left1_eq_2_2_1
  · exact cols_left1_eq_2_3_0
  · exact cols_left1_eq_2_3_1
  · exact cols_left1_eq_3_0_0
  · exact cols_left1_eq_3_0_1
  · exact cols_left1_eq_3_1_0
  · exact cols_left1_eq_3_1_1
  · exact cols_left1_eq_3_2_0
  · exact cols_left1_eq_3_2_1
  · exact cols_left1_eq_3_3_0
  · exact cols_left1_eq_3_3_1

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 65 32 5076528897714338582849363683428990140844217677231884780544,
    decodeIntegerRow 32 65 32 78100728902297805406684571901552839318219201323139515392,
    decodeIntegerRow 32 65 32 5076565859451855910720012612424575690984514014008643380480,
    decodeIntegerRow 32 65 32 80503250587225592641795175694169563357654236986781951232,
    decodeIntegerRow 32 65 32 10228754856333941865149443740061421426635269143924264379392,
    decodeIntegerRow 32 65 32 5232692807232574622602961096594032741529482964946143110144,
    decodeIntegerRow 32 65 32 10231157378022947182210082968499257455586982966854371935232,
    decodeIntegerRow 32 65 32 5232729769239271650186584307937865759837299936763134510080,
    decodeIntegerRow 32 65 32 5232692238722978698276254930041431784734514327676969510144,
    decodeIntegerRow 32 65 32 10228754847587640389390571337499073719607654241812430939392,
    decodeIntegerRow 32 65 32 5232729200460495045967895888506839064184061741048728110080,
    decodeIntegerRow 32 65 32 10231157369272504465222103146661857044884625456151073375232,
    decodeIntegerRow 32 65 32 10231157378022979030372006394527275534637914889798371935232,
    decodeIntegerRow 32 65 32 5232729769239272140156522480700155105387597610900734510080,
    decodeIntegerRow 32 65 32 10228754856333910001907898191199109778418119923668264379392,
    decodeIntegerRow 32 65 32 5232692807232574132401029581893882463523905793803743110144,
    decodeIntegerRow 32 65 32 78100728902297805406684571903090518535478621095073375232,
    decodeIntegerRow 32 65 32 5076528897714338582849363683528938926105802645186328110080,
    decodeIntegerRow 32 65 32 10228754847587608526148970865772129766754242947924281951232,
    decodeIntegerRow 32 65 32 5232692238722978208070753429140181341339342724946143380480,
    decodeIntegerRow 32 65 32 5232692807232574622602961096694028850854149857472069780480,
    decodeIntegerRow 32 65 32 10228754856333941865149443740062959822716686178493948511232,
    decodeIntegerRow 32 65 32 5076528328935562468604181733626843948078828647700634510080,
    decodeIntegerRow 32 65 32 78100720151886936580683072967041135258751677791871935232,
    decodeIntegerRow 32 65 32 10228754847587640389390571337497535312322583619668281951232,
    decodeIntegerRow 32 65 32 5232692238722978698276254929941435675237483533803743380480,
    decodeIntegerRow 32 65 32 78100728902329653568662894801366198724941706151073375232,
    decodeIntegerRow 32 65 32 5076528897714339072822870152857973073381180491048728110080,
    decodeIntegerRow 32 65 32 5232729769239272140156522480800103890476900250579978380544,
    decodeIntegerRow 32 65 32 10231157378022979030372006394528813202656822971682340955392,
    decodeIntegerRow 32 65 32 5076565290942259986389736459670874568627587043803743110144,
    decodeIntegerRow 32 65 32 80503241840924116882867850267189540490123673668264379392]

def cols_right2 (r : LeftIndex 5 5 5) : List ℤ := cols_right2Data.getD (leftPosition 5 5 5 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_2_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_2_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_3_0 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2))) = cols_right2 ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_3_1 : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2))) = cols_right2 ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 5 5 5) : (tripleIndices 4 4 2).map (fun j => (right2Middle5 5 5) j r) = cols_right2 r := by
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
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_2_0
  · exact cols_right2_eq_2_2_1
  · exact cols_right2_eq_2_3_0
  · exact cols_right2_eq_2_3_1
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_2_0
  · exact cols_right2_eq_3_2_1
  · exact cols_right2_eq_3_3_0
  · exact cols_right2_eq_3_3_1

theorem product0_eq : HexagonAtoms555.outerABC * HexagonAtoms555.assocABC = HexagonAtoms555.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 4 × Fin 2) (n := Fin 4 × Fin 4 × Fin 2) _

theorem product1_eq : HexagonAtoms555.assocABC * HexagonAtoms555.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms555.innerRightABC * HexagonAtoms555.assocABC = rowColumnMul rows_innerRightABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_assocABC_data).symm

theorem product3_eq : HexagonAtoms555.inverseACB * right0Middle5 5 5 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms555.innerABC * right1Middle5 5 5 = rowColumnMul rows_innerABC cols_right1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerABC_data cols_right1_data).symm

theorem product5_eq : HexagonAtoms555.assocABC * left0Middle5 5 5 = rowColumnMul rows_assocABC cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms555.innerRightABC * left1Middle5 5 5 = rowColumnMul rows_innerRightABC cols_left1 :=
  (rowColumnMul_eq _ _ _ _ rows_innerRightABC_data cols_left1_data).symm

theorem product7_eq : HexagonAtoms555.assocABC * right2Middle5 5 5 = rowColumnMul rows_assocABC cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn555
