import RMod.BrundanEllis.StackingReferenceHexagonAtoms336
import RMod.BrundanEllis.StackingReferenceHexagonMiddle3
import RMod.BrundanEllis.StackingReferenceRowColumnCheck

/-! Verified row and column lists. Each subsequent scalar product traverses
these lists directly, without repeated lookup into the original matrices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn336
open Superfusion

theorem assocBAC_alias : HexagonAtoms336.assocBAC = HexagonAtoms336.assocABC :=
  HexagonAtoms336.assocBAC_eq.symm.trans HexagonAtoms336.assocABC_eq

theorem innerRightBAC_alias : HexagonAtoms336.innerRightBAC = HexagonAtoms336.innerRightABC :=
  HexagonAtoms336.innerRightBAC_eq.symm.trans HexagonAtoms336.innerRightABC_eq

private def rows_outerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425917,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094425893,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425191,
    decodeIntegerRow 32 3 1 926510094423733,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
    decodeIntegerRow 32 3 1 926510137472641,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510481846409,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926513581210321,
    decodeIntegerRow 32 3 1 926520554779123,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926792523962401,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 929051960254249,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 949386886880881,
    decodeIntegerRow 32 3 1 995140471790803,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 1544183490709867]

def rows_outerABC (r : LeftIndex 3 6 3) : List ℤ := rows_outerABCData.getD (leftPosition 3 6 3 r) []

private theorem rows_outerABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_outerABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_outerABC_data (r : LeftIndex 3 6 3) : (tripleIndices 4 2 4).map ((HexagonAtoms336.outerABC) r) = rows_outerABC r := by
  fin_cases r
  · exact rows_outerABC_eq_0_0_0
  · exact rows_outerABC_eq_0_0_1
  · exact rows_outerABC_eq_0_0_2
  · exact rows_outerABC_eq_0_0_3
  · exact rows_outerABC_eq_0_1_0
  · exact rows_outerABC_eq_0_1_1
  · exact rows_outerABC_eq_0_1_2
  · exact rows_outerABC_eq_0_1_3
  · exact rows_outerABC_eq_1_0_0
  · exact rows_outerABC_eq_1_0_1
  · exact rows_outerABC_eq_1_0_2
  · exact rows_outerABC_eq_1_0_3
  · exact rows_outerABC_eq_1_1_0
  · exact rows_outerABC_eq_1_1_1
  · exact rows_outerABC_eq_1_1_2
  · exact rows_outerABC_eq_1_1_3
  · exact rows_outerABC_eq_2_0_0
  · exact rows_outerABC_eq_2_0_1
  · exact rows_outerABC_eq_2_0_2
  · exact rows_outerABC_eq_2_0_3
  · exact rows_outerABC_eq_2_1_0
  · exact rows_outerABC_eq_2_1_1
  · exact rows_outerABC_eq_2_1_2
  · exact rows_outerABC_eq_2_1_3
  · exact rows_outerABC_eq_3_0_0
  · exact rows_outerABC_eq_3_0_1
  · exact rows_outerABC_eq_3_0_2
  · exact rows_outerABC_eq_3_0_3
  · exact rows_outerABC_eq_3_1_0
  · exact rows_outerABC_eq_3_1_1
  · exact rows_outerABC_eq_3_1_2
  · exact rows_outerABC_eq_3_1_3

private def rows_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 1521306698438614,
    decodeIntegerRow 32 3 1 1063770849234418,
    decodeIntegerRow 32 3 1 651988585005754,
    decodeIntegerRow 32 3 1 285959905857598,
    decodeIntegerRow 32 3 1 926510352705274,
    decodeIntegerRow 32 3 1 926508975213442,
    decodeIntegerRow 32 3 1 926508889115626,
    decodeIntegerRow 32 3 1 926510610987058,
    decodeIntegerRow 32 3 1 651988584927022,
    decodeIntegerRow 32 3 1 1567060283335414,
    decodeIntegerRow 32 3 1 331713490780642,
    decodeIntegerRow 32 3 1 1063770849076954,
    decodeIntegerRow 32 3 1 926511299732002,
    decodeIntegerRow 32 3 1 926510610986086,
    decodeIntegerRow 32 3 1 926510352707218,
    decodeIntegerRow 32 3 1 926511213642934,
    decodeIntegerRow 32 3 1 924815523584326,
    decodeIntegerRow 32 3 1 933853247494078,
    decodeIntegerRow 32 3 1 934418135264854,
    decodeIntegerRow 32 3 1 923120936799502,
    decodeIntegerRow 32 3 1 926419438031466,
    decodeIntegerRow 32 3 1 926489173719502,
    decodeIntegerRow 32 3 1 926551935838726,
    decodeIntegerRow 32 3 1 926607724389122,
    decodeIntegerRow 32 3 1 918602081221918,
    decodeIntegerRow 32 3 1 923120943176794,
    decodeIntegerRow 32 3 1 924815510829742,
    decodeIntegerRow 32 3 1 919166911597066,
    decodeIntegerRow 32 3 1 926551935838738,
    decodeIntegerRow 32 3 1 926412464462666,
    decodeIntegerRow 32 3 1 926600750820318,
    decodeIntegerRow 32 3 1 926489173719526]

def rows_assocABC (r : RightIndex 3 3 6) : List ℤ := rows_assocABCData.getD (rightPosition 3 3 6 r) []

private theorem rows_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocABC_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocABC_data (r : RightIndex 3 3 6) : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocABC) r) = rows_assocABC r := by
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
  · exact rows_assocABC_eq_2_0_0
  · exact rows_assocABC_eq_2_0_1
  · exact rows_assocABC_eq_2_0_2
  · exact rows_assocABC_eq_2_0_3
  · exact rows_assocABC_eq_2_1_0
  · exact rows_assocABC_eq_2_1_1
  · exact rows_assocABC_eq_2_1_2
  · exact rows_assocABC_eq_2_1_3
  · exact rows_assocABC_eq_3_0_0
  · exact rows_assocABC_eq_3_0_1
  · exact rows_assocABC_eq_3_0_2
  · exact rows_assocABC_eq_3_0_3
  · exact rows_assocABC_eq_3_1_0
  · exact rows_assocABC_eq_3_1_1
  · exact rows_assocABC_eq_3_1_2
  · exact rows_assocABC_eq_3_1_3

private def rows_inverseACBData : List (List ℤ) := [decodeIntegerRow 32 3 1 936676773335236,
    decodeIntegerRow 32 3 1 921424793953972,
    decodeIntegerRow 32 3 1 925380463435996,
    decodeIntegerRow 32 3 1 927075127811692,
    decodeIntegerRow 32 3 1 1750137384805600,
    decodeIntegerRow 32 3 1 514853354238880,
    decodeIntegerRow 32 3 1 834995951050400,
    decodeIntegerRow 32 3 1 972249732224480,
    decodeIntegerRow 32 3 1 921424832220640,
    decodeIntegerRow 32 3 1 916343396390560,
    decodeIntegerRow 32 3 1 927075123559840,
    decodeIntegerRow 32 3 1 927639727540960,
    decodeIntegerRow 32 3 1 1338166834140604,
    decodeIntegerRow 32 3 1 1750137385041868,
    decodeIntegerRow 32 3 1 880770456679844,
    decodeIntegerRow 32 3 1 834995951024148,
    decodeIntegerRow 32 3 1 1338417882617440,
    decodeIntegerRow 32 3 1 1750011860803360,
    decodeIntegerRow 32 3 1 880742562404640,
    decodeIntegerRow 32 3 1 835009898161760,
    decodeIntegerRow 32 3 1 931592257270204,
    decodeIntegerRow 32 3 1 936678342149068,
    decodeIntegerRow 32 3 1 925945409665444,
    decodeIntegerRow 32 3 1 925380289123348,
    decodeIntegerRow 32 3 1 1750011860567236,
    decodeIntegerRow 32 3 1 514602305761972,
    decodeIntegerRow 32 3 1 835009898187996,
    decodeIntegerRow 32 3 1 972277626499692,
    decodeIntegerRow 32 3 1 916341865840480,
    decodeIntegerRow 32 3 1 931592295531040,
    decodeIntegerRow 32 3 1 927639897602080,
    decodeIntegerRow 32 3 1 925945405414240]

def rows_inverseACB (r : LeftIndex 3 6 3) : List ℤ := rows_inverseACBData.getD (leftPosition 3 6 3 r) []

private theorem rows_inverseACB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_inverseACB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_inverseACB_data (r : LeftIndex 3 6 3) : (tripleIndices 4 2 4).map ((HexagonAtoms336.inverseACB) r) = rows_inverseACB r := by
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
  · exact rows_inverseACB_eq_2_0_0
  · exact rows_inverseACB_eq_2_0_1
  · exact rows_inverseACB_eq_2_0_2
  · exact rows_inverseACB_eq_2_0_3
  · exact rows_inverseACB_eq_2_1_0
  · exact rows_inverseACB_eq_2_1_1
  · exact rows_inverseACB_eq_2_1_2
  · exact rows_inverseACB_eq_2_1_3
  · exact rows_inverseACB_eq_3_0_0
  · exact rows_inverseACB_eq_3_0_1
  · exact rows_inverseACB_eq_3_0_2
  · exact rows_inverseACB_eq_3_0_3
  · exact rows_inverseACB_eq_3_1_0
  · exact rows_inverseACB_eq_3_1_1
  · exact rows_inverseACB_eq_3_1_2
  · exact rows_inverseACB_eq_3_1_3

private def rows_assocBCAData : List (List ℤ) := [decodeIntegerRow 32 3 1 916343396390560,
    decodeIntegerRow 32 3 1 931595356631200,
    decodeIntegerRow 32 3 1 927639727540960,
    decodeIntegerRow 32 3 1 925945065292000,
    decodeIntegerRow 32 3 1 102882803809972,
    decodeIntegerRow 32 3 1 1338166834140604,
    decodeIntegerRow 32 3 1 1018024237827692,
    decodeIntegerRow 32 3 1 880770456679844,
    decodeIntegerRow 32 3 1 931595394897868,
    decodeIntegerRow 32 3 1 936676773335236,
    decodeIntegerRow 32 3 1 925945061040148,
    decodeIntegerRow 32 3 1 925380463435996,
    decodeIntegerRow 32 3 1 514853354238880,
    decodeIntegerRow 32 3 1 102882804046240,
    decodeIntegerRow 32 3 1 972249732224480,
    decodeIntegerRow 32 3 1 1018024237801440,
    decodeIntegerRow 32 3 1 1338417883089868,
    decodeIntegerRow 32 3 1 1750011860567236,
    decodeIntegerRow 32 3 1 880742562352148,
    decodeIntegerRow 32 3 1 835009898187996,
    decodeIntegerRow 32 3 1 931592295531040,
    decodeIntegerRow 32 3 1 936678323011360,
    decodeIntegerRow 32 3 1 925945405414240,
    decodeIntegerRow 32 3 1 925380291249760,
    decodeIntegerRow 32 3 1 1750011860803360,
    decodeIntegerRow 32 3 1 514602306234400,
    decodeIntegerRow 32 3 1 835009898161760,
    decodeIntegerRow 32 3 1 972277626447200,
    decodeIntegerRow 32 3 1 916341846702772,
    decodeIntegerRow 32 3 1 931592257270204,
    decodeIntegerRow 32 3 1 927639899728492,
    decodeIntegerRow 32 3 1 925945409665444]

def rows_assocBCA (r : RightIndex 3 6 3) : List ℤ := rows_assocBCAData.getD (rightPosition 3 6 3 r) []

private theorem rows_assocBCA_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocBCA_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocBCA_data (r : RightIndex 3 6 3) : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocBCA) r) = rows_assocBCA r := by
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
  · exact rows_assocBCA_eq_2_0_0
  · exact rows_assocBCA_eq_2_0_1
  · exact rows_assocBCA_eq_2_0_2
  · exact rows_assocBCA_eq_2_0_3
  · exact rows_assocBCA_eq_2_1_0
  · exact rows_assocBCA_eq_2_1_1
  · exact rows_assocBCA_eq_2_1_2
  · exact rows_assocBCA_eq_2_1_3
  · exact rows_assocBCA_eq_3_0_0
  · exact rows_assocBCA_eq_3_0_1
  · exact rows_assocBCA_eq_3_0_2
  · exact rows_assocBCA_eq_3_0_3
  · exact rows_assocBCA_eq_3_1_0
  · exact rows_assocBCA_eq_3_1_1
  · exact rows_assocBCA_eq_3_1_2
  · exact rows_assocBCA_eq_3_1_3

private def rows_assocCABData : List (List ℤ) := [decodeIntegerRow 32 3 1 925945417108696,
    decodeIntegerRow 32 3 1 927639917795704,
    decodeIntegerRow 32 3 1 921427911388012,
    decodeIntegerRow 32 3 1 936678330454612,
    decodeIntegerRow 32 3 1 1338166834363656,
    decodeIntegerRow 32 3 1 1750137384949976,
    decodeIntegerRow 32 3 1 880770456535468,
    decodeIntegerRow 32 3 1 834995951273452,
    decodeIntegerRow 32 3 1 931595374701976,
    decodeIntegerRow 32 3 1 936676785024184,
    decodeIntegerRow 32 3 1 925945053603052,
    decodeIntegerRow 32 3 1 925380481506772,
    decodeIntegerRow 32 3 1 880742562496456,
    decodeIntegerRow 32 3 1 1018010290913176,
    decodeIntegerRow 32 3 1 514602305985068,
    decodeIntegerRow 32 3 1 1750011860659052,
    decodeIntegerRow 32 3 1 880770456771736,
    decodeIntegerRow 32 3 1 1018024238050744,
    decodeIntegerRow 32 3 1 514853354461932,
    decodeIntegerRow 32 3 1 1750137384897492,
    decodeIntegerRow 32 3 1 921427913514424,
    decodeIntegerRow 32 3 1 916341854146024,
    decodeIntegerRow 32 3 1 927074790880852,
    decodeIntegerRow 32 3 1 927639879534868,
    decodeIntegerRow 32 3 1 1338417882840536,
    decodeIntegerRow 32 3 1 1750011860711544,
    decodeIntegerRow 32 3 1 880742562260332,
    decodeIntegerRow 32 3 1 835009898411092,
    decodeIntegerRow 32 3 1 927075116122744,
    decodeIntegerRow 32 3 1 925380443240104,
    decodeIntegerRow 32 3 1 931595376827092,
    decodeIntegerRow 32 3 1 916343408079508]

def rows_assocCAB (r : RightIndex 6 3 3) : List ℤ := rows_assocCABData.getD (rightPosition 6 3 3 r) []

private theorem rows_assocCAB_eq_0_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_0_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_1_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_2_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_0_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_0 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_1 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_2 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem rows_assocCAB_eq_3_1_3 : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = rows_assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem rows_assocCAB_data (r : RightIndex 6 3 3) : (tripleIndices 4 2 4).map ((HexagonAtoms336.assocCAB) r) = rows_assocCAB r := by
  fin_cases r
  · exact rows_assocCAB_eq_0_0_0
  · exact rows_assocCAB_eq_0_0_1
  · exact rows_assocCAB_eq_0_0_2
  · exact rows_assocCAB_eq_0_0_3
  · exact rows_assocCAB_eq_0_1_0
  · exact rows_assocCAB_eq_0_1_1
  · exact rows_assocCAB_eq_0_1_2
  · exact rows_assocCAB_eq_0_1_3
  · exact rows_assocCAB_eq_1_0_0
  · exact rows_assocCAB_eq_1_0_1
  · exact rows_assocCAB_eq_1_0_2
  · exact rows_assocCAB_eq_1_0_3
  · exact rows_assocCAB_eq_1_1_0
  · exact rows_assocCAB_eq_1_1_1
  · exact rows_assocCAB_eq_1_1_2
  · exact rows_assocCAB_eq_1_1_3
  · exact rows_assocCAB_eq_2_0_0
  · exact rows_assocCAB_eq_2_0_1
  · exact rows_assocCAB_eq_2_0_2
  · exact rows_assocCAB_eq_2_0_3
  · exact rows_assocCAB_eq_2_1_0
  · exact rows_assocCAB_eq_2_1_1
  · exact rows_assocCAB_eq_2_1_2
  · exact rows_assocCAB_eq_2_1_3
  · exact rows_assocCAB_eq_3_0_0
  · exact rows_assocCAB_eq_3_0_1
  · exact rows_assocCAB_eq_3_0_2
  · exact rows_assocCAB_eq_3_0_3
  · exact rows_assocCAB_eq_3_1_0
  · exact rows_assocCAB_eq_3_1_1
  · exact rows_assocCAB_eq_3_1_2
  · exact rows_assocCAB_eq_3_1_3

private def cols_assocABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 789339996090580,
    decodeIntegerRow 32 3 1 1521327618961312,
    decodeIntegerRow 32 3 1 1567018441752016,
    decodeIntegerRow 32 3 1 651890955003160,
    decodeIntegerRow 32 3 1 926510109307240,
    decodeIntegerRow 32 3 1 926510100800944,
    decodeIntegerRow 32 3 1 926510097616672,
    decodeIntegerRow 32 3 1 926510108242900,
    decodeIntegerRow 32 3 1 926510094465260,
    decodeIntegerRow 32 3 1 926510094255328,
    decodeIntegerRow 32 3 1 926510094242224,
    decodeIntegerRow 32 3 1 926510094504680,
    decodeIntegerRow 32 3 1 918601550843800,
    decodeIntegerRow 32 3 1 923122145296336,
    decodeIntegerRow 32 3 1 924814397992288,
    decodeIntegerRow 32 3 1 919167184757740,
    decodeIntegerRow 32 3 1 926510080607968,
    decodeIntegerRow 32 3 1 926510091239380,
    decodeIntegerRow 32 3 1 926510100805480,
    decodeIntegerRow 32 3 1 926510109305296,
    decodeIntegerRow 32 3 1 652086214929616,
    decodeIntegerRow 32 3 1 1567102124577640,
    decodeIntegerRow 32 3 1 331734411303340,
    decodeIntegerRow 32 3 1 1063861505550112,
    decodeIntegerRow 32 3 1 933853520654752,
    decodeIntegerRow 32 3 1 928203552430060,
    decodeIntegerRow 32 3 1 923119734679960,
    decodeIntegerRow 32 3 1 918602583965104,
    decodeIntegerRow 32 3 1 926510094504624,
    decodeIntegerRow 32 3 1 926510094242200,
    decodeIntegerRow 32 3 1 926510094596500,
    decodeIntegerRow 32 3 1 926510094386528]

def cols_assocABC (r : LeftIndex 3 3 6) : List ℤ := cols_assocABCData.getD (leftPosition 3 3 6 r) []

private theorem cols_assocABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_assocABC_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_assocABC_data (r : LeftIndex 3 3 6) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.assocABC) j r) = cols_assocABC r := by
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
  · exact cols_assocABC_eq_2_0_0
  · exact cols_assocABC_eq_2_0_1
  · exact cols_assocABC_eq_2_0_2
  · exact cols_assocABC_eq_2_0_3
  · exact cols_assocABC_eq_2_1_0
  · exact cols_assocABC_eq_2_1_1
  · exact cols_assocABC_eq_2_1_2
  · exact cols_assocABC_eq_2_1_3
  · exact cols_assocABC_eq_3_0_0
  · exact cols_assocABC_eq_3_0_1
  · exact cols_assocABC_eq_3_0_2
  · exact cols_assocABC_eq_3_0_3
  · exact cols_assocABC_eq_3_1_0
  · exact cols_assocABC_eq_3_1_1
  · exact cols_assocABC_eq_3_1_2
  · exact cols_assocABC_eq_3_1_3

private def cols_innerABCData : List (List ℤ) := [decodeIntegerRow 32 3 1 927639642511048,
    decodeIntegerRow 32 3 1 927074868468484,
    decodeIntegerRow 32 3 1 936676027192072,
    decodeIntegerRow 32 3 1 931593060808996,
    decodeIntegerRow 32 3 1 880763483071676,
    decodeIntegerRow 32 3 1 1018003317134408,
    decodeIntegerRow 32 3 1 514790592237724,
    decodeIntegerRow 32 3 1 1749949098802312,
    decodeIntegerRow 32 3 1 925380550592968,
    decodeIntegerRow 32 3 1 925945322509444,
    decodeIntegerRow 32 3 1 916344199929352,
    decodeIntegerRow 32 3 1 921427147177636,
    decodeIntegerRow 32 3 1 972256705753916,
    decodeIntegerRow 32 3 1 835016871769928,
    decodeIntegerRow 32 3 1 1338229596377884,
    decodeIntegerRow 32 3 1 103071090521992,
    decodeIntegerRow 32 3 1 880749535934076,
    decodeIntegerRow 32 3 1 1018031211409608,
    decodeIntegerRow 32 3 1 514665067999324,
    decodeIntegerRow 32 3 1 1750200147279112,
    decodeIntegerRow 32 3 1 927639986884168,
    decodeIntegerRow 32 3 1 927075040655044,
    decodeIntegerRow 32 3 1 936679126550152,
    decodeIntegerRow 32 3 1 931594610488036,
    decodeIntegerRow 32 3 1 880749535960316,
    decodeIntegerRow 32 3 1 1018031211357128,
    decodeIntegerRow 32 3 1 514665068235484,
    decodeIntegerRow 32 3 1 1750200146806792,
    decodeIntegerRow 32 3 1 927639982633288,
    decodeIntegerRow 32 3 1 927075038529604,
    decodeIntegerRow 32 3 1 936679088292232,
    decodeIntegerRow 32 3 1 931594591359076]

def cols_innerABC (r : LeftIndex 3 3 6) : List ℤ := cols_innerABCData.getD (leftPosition 3 3 6 r) []

private theorem cols_innerABC_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_innerABC_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_innerABC_data (r : LeftIndex 3 3 6) : (tripleIndices 4 2 4).map (fun j => (HexagonAtoms336.innerABC) j r) = cols_innerABC r := by
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
  · exact cols_innerABC_eq_2_0_0
  · exact cols_innerABC_eq_2_0_1
  · exact cols_innerABC_eq_2_0_2
  · exact cols_innerABC_eq_2_0_3
  · exact cols_innerABC_eq_2_1_0
  · exact cols_innerABC_eq_2_1_1
  · exact cols_innerABC_eq_2_1_2
  · exact cols_innerABC_eq_2_1_3
  · exact cols_innerABC_eq_3_0_0
  · exact cols_innerABC_eq_3_0_1
  · exact cols_innerABC_eq_3_0_2
  · exact cols_innerABC_eq_3_0_3
  · exact cols_innerABC_eq_3_1_0
  · exact cols_innerABC_eq_3_1_1
  · exact cols_innerABC_eq_3_1_2
  · exact cols_innerABC_eq_3_1_3

private def cols_right0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789339996090580,
    decodeIntegerRow 32 3 1 1521327618961312,
    decodeIntegerRow 32 3 1 1567018441752016,
    decodeIntegerRow 32 3 1 651890955003160,
    decodeIntegerRow 32 3 1 926510109307240,
    decodeIntegerRow 32 3 1 926510100800944,
    decodeIntegerRow 32 3 1 926510097616672,
    decodeIntegerRow 32 3 1 926510108242900,
    decodeIntegerRow 32 3 1 926510094465260,
    decodeIntegerRow 32 3 1 926510094255328,
    decodeIntegerRow 32 3 1 926510094242224,
    decodeIntegerRow 32 3 1 926510094504680,
    decodeIntegerRow 32 3 1 918601550843800,
    decodeIntegerRow 32 3 1 923122145296336,
    decodeIntegerRow 32 3 1 924814397992288,
    decodeIntegerRow 32 3 1 919167184757740,
    decodeIntegerRow 32 3 1 926510080607968,
    decodeIntegerRow 32 3 1 926510091239380,
    decodeIntegerRow 32 3 1 926510100805480,
    decodeIntegerRow 32 3 1 926510109305296,
    decodeIntegerRow 32 3 1 652086214929616,
    decodeIntegerRow 32 3 1 1567102124577640,
    decodeIntegerRow 32 3 1 331734411303340,
    decodeIntegerRow 32 3 1 1063861505550112,
    decodeIntegerRow 32 3 1 933853520654752,
    decodeIntegerRow 32 3 1 928203552430060,
    decodeIntegerRow 32 3 1 923119734679960,
    decodeIntegerRow 32 3 1 918602583965104,
    decodeIntegerRow 32 3 1 926510094504624,
    decodeIntegerRow 32 3 1 926510094242200,
    decodeIntegerRow 32 3 1 926510094596500,
    decodeIntegerRow 32 3 1 926510094386528]

def cols_right0 (r : LeftIndex 3 3 6) : List ℤ := cols_right0Data.getD (leftPosition 3 3 6 r) []

private theorem cols_right0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right0_data (r : LeftIndex 3 3 6) : (tripleIndices 4 2 4).map (fun j => (right0Middle3 3 6) j r) = cols_right0 r := by
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
  · exact cols_right0_eq_2_0_0
  · exact cols_right0_eq_2_0_1
  · exact cols_right0_eq_2_0_2
  · exact cols_right0_eq_2_0_3
  · exact cols_right0_eq_2_1_0
  · exact cols_right0_eq_2_1_1
  · exact cols_right0_eq_2_1_2
  · exact cols_right0_eq_2_1_3
  · exact cols_right0_eq_3_0_0
  · exact cols_right0_eq_3_0_1
  · exact cols_right0_eq_3_0_2
  · exact cols_right0_eq_3_0_3
  · exact cols_right0_eq_3_1_0
  · exact cols_right0_eq_3_1_1
  · exact cols_right0_eq_3_1_2
  · exact cols_right0_eq_3_1_3

private def cols_left0Data : List (List ℤ) := [decodeIntegerRow 32 3 1 789339996090580,
    decodeIntegerRow 32 3 1 1521327618961312,
    decodeIntegerRow 32 3 1 1567018441752016,
    decodeIntegerRow 32 3 1 651890955003160,
    decodeIntegerRow 32 3 1 926510079544600,
    decodeIntegerRow 32 3 1 926510088050896,
    decodeIntegerRow 32 3 1 926510091235168,
    decodeIntegerRow 32 3 1 926510080608940,
    decodeIntegerRow 32 3 1 926510094386580,
    decodeIntegerRow 32 3 1 926510094596512,
    decodeIntegerRow 32 3 1 926510094609616,
    decodeIntegerRow 32 3 1 926510094347160,
    decodeIntegerRow 32 3 1 918601550843800,
    decodeIntegerRow 32 3 1 923122145296336,
    decodeIntegerRow 32 3 1 924814397992288,
    decodeIntegerRow 32 3 1 919167184757740,
    decodeIntegerRow 32 3 1 926510108243872,
    decodeIntegerRow 32 3 1 926510097612460,
    decodeIntegerRow 32 3 1 926510088046360,
    decodeIntegerRow 32 3 1 926510079546544,
    decodeIntegerRow 32 3 1 652086214929616,
    decodeIntegerRow 32 3 1 1567102124577640,
    decodeIntegerRow 32 3 1 331734411303340,
    decodeIntegerRow 32 3 1 1063861505550112,
    decodeIntegerRow 32 3 1 933853520654752,
    decodeIntegerRow 32 3 1 928203552430060,
    decodeIntegerRow 32 3 1 923119734679960,
    decodeIntegerRow 32 3 1 918602583965104,
    decodeIntegerRow 32 3 1 926510094347216,
    decodeIntegerRow 32 3 1 926510094609640,
    decodeIntegerRow 32 3 1 926510094255340,
    decodeIntegerRow 32 3 1 926510094465312]

def cols_left0 (r : LeftIndex 3 3 6) : List ℤ := cols_left0Data.getD (leftPosition 3 3 6 r) []

private theorem cols_left0_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_left0_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_left0 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_left0_data (r : LeftIndex 3 3 6) : (tripleIndices 4 2 4).map (fun j => (left0Middle3 3 6) j r) = cols_left0 r := by
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
  · exact cols_left0_eq_2_0_0
  · exact cols_left0_eq_2_0_1
  · exact cols_left0_eq_2_0_2
  · exact cols_left0_eq_2_0_3
  · exact cols_left0_eq_2_1_0
  · exact cols_left0_eq_2_1_1
  · exact cols_left0_eq_2_1_2
  · exact cols_left0_eq_2_1_3
  · exact cols_left0_eq_3_0_0
  · exact cols_left0_eq_3_0_1
  · exact cols_left0_eq_3_0_2
  · exact cols_left0_eq_3_0_3
  · exact cols_left0_eq_3_1_0
  · exact cols_left0_eq_3_1_1
  · exact cols_left0_eq_3_1_2
  · exact cols_left0_eq_3_1_3

private def cols_right2Data : List (List ℤ) := [decodeIntegerRow 32 5 2 11640816925662231570312,
    decodeIntegerRow 32 5 2 11641055347415161320312,
    decodeIntegerRow 32 5 2 11623650758746215815312,
    decodeIntegerRow 32 5 2 11629611299512817375312,
    decodeIntegerRow 32 5 2 12088567781448247070512,
    decodeIntegerRow 32 5 2 11939554262161333008112,
    decodeIntegerRow 32 5 2 22817422151565556445304,
    decodeIntegerRow 32 5 2 19092084169387814257800,
    decodeIntegerRow 32 5 2 11623650819775512690312,
    decodeIntegerRow 32 5 2 11653453157422973640312,
    decodeIntegerRow 32 5 2 11642247437136840695312,
    decodeIntegerRow 32 5 2 11641055343655395695312,
    decodeIntegerRow 32 5 2 465680360794072070320,
    decodeIntegerRow 32 5 2 19092141389846804882800,
    decodeIntegerRow 32 5 2 12088566255569575195512,
    decodeIntegerRow 32 5 2 11343507814407426757512,
    decodeIntegerRow 32 5 2 11194496583938481445512,
    decodeIntegerRow 32 5 2 11343510103225786133112,
    decodeIntegerRow 32 5 2 465642213821415820304,
    decodeIntegerRow 32 5 2 4190980195999142382800,
    decodeIntegerRow 32 5 2 11640816925808715695312,
    decodeIntegerRow 32 5 2 11641055347317504695312,
    decodeIntegerRow 32 5 2 11623650758740356450312,
    decodeIntegerRow 32 5 2 11629611299516723640312,
    decodeIntegerRow 32 5 2 465680360794062695304,
    decodeIntegerRow 32 5 2 19092141389846798632824,
    decodeIntegerRow 32 5 2 12088566255569340820112,
    decodeIntegerRow 32 5 2 11343507814407270508112,
    decodeIntegerRow 32 5 2 11659413545605590815312,
    decodeIntegerRow 32 5 2 11629611207960083015312,
    decodeIntegerRow 32 5 2 11640816928103637570312,
    decodeIntegerRow 32 5 2 11642009021633911320312]

def cols_right2 (r : LeftIndex 3 3 6) : List ℤ := cols_right2Data.getD (leftPosition 3 3 6 r) []

private theorem cols_right2_eq_0_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_0_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_1_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_2_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_0_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_0 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_1 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_2 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

private theorem cols_right2_eq_3_1_3 : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4))) = cols_right2 ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleVectorCheck_sound
  decide +kernel

theorem cols_right2_data (r : LeftIndex 3 3 6) : (tripleIndices 4 2 4).map (fun j => (right2Middle3 3 6) j r) = cols_right2 r := by
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
  · exact cols_right2_eq_2_0_0
  · exact cols_right2_eq_2_0_1
  · exact cols_right2_eq_2_0_2
  · exact cols_right2_eq_2_0_3
  · exact cols_right2_eq_2_1_0
  · exact cols_right2_eq_2_1_1
  · exact cols_right2_eq_2_1_2
  · exact cols_right2_eq_2_1_3
  · exact cols_right2_eq_3_0_0
  · exact cols_right2_eq_3_0_1
  · exact cols_right2_eq_3_0_2
  · exact cols_right2_eq_3_0_3
  · exact cols_right2_eq_3_1_0
  · exact cols_right2_eq_3_1_1
  · exact cols_right2_eq_3_1_2
  · exact cols_right2_eq_3_1_3

theorem product0_eq : HexagonAtoms336.outerABC * HexagonAtoms336.assocABC = rowColumnMul rows_outerABC cols_assocABC :=
  (rowColumnMul_eq _ _ _ _ rows_outerABC_data cols_assocABC_data).symm

theorem product1_eq : HexagonAtoms336.assocABC * HexagonAtoms336.innerABC = rowColumnMul rows_assocABC cols_innerABC :=
  (rowColumnMul_eq _ _ _ _ rows_assocABC_data cols_innerABC_data).symm

theorem product2_eq : HexagonAtoms336.innerRightABC * HexagonAtoms336.assocABC = HexagonAtoms336.assocABC :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product3_eq : HexagonAtoms336.inverseACB * right0Middle3 3 6 = rowColumnMul rows_inverseACB cols_right0 :=
  (rowColumnMul_eq _ _ _ _ rows_inverseACB_data cols_right0_data).symm

theorem product4_eq : HexagonAtoms336.innerACB * right1Middle3 3 6 = right1Middle3 3 6 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product5_eq : HexagonAtoms336.assocBCA * left0Middle3 3 6 = rowColumnMul rows_assocBCA cols_left0 :=
  (rowColumnMul_eq _ _ _ _ rows_assocBCA_data cols_left0_data).symm

theorem product6_eq : HexagonAtoms336.innerRightABC * left1Middle3 3 6 = left1Middle3 3 6 :=
  Matrix.one_mul (m := Fin 4 × Fin 2 × Fin 4) (n := Fin 4 × Fin 2 × Fin 4) _

theorem product7_eq : HexagonAtoms336.assocCAB * right2Middle3 3 6 = rowColumnMul rows_assocCAB cols_right2 :=
  (rowColumnMul_eq _ _ _ _ rows_assocCAB_data cols_right2_data).symm

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonRowColumn336
