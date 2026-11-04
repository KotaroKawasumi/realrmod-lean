import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms336
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1521306698438614,
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

def assocABC : Matrix (RightIndex 3 3 6) (LeftIndex 3 3 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 3 6 r) []).getD (leftPosition 3 3 6 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_2 : (associatorZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_3 : (associatorZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_2 : (associatorZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_3 : (associatorZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 3 6 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_0_2
  · exact assocABC_row_0_0_3
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_1_2
  · exact assocABC_row_0_1_3
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_1_2
  · exact assocABC_row_1_1_3
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_0_2
  · exact assocABC_row_2_0_3
  · exact assocABC_row_2_1_0
  · exact assocABC_row_2_1_1
  · exact assocABC_row_2_1_2
  · exact assocABC_row_2_1_3
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_0_2
  · exact assocABC_row_3_0_3
  · exact assocABC_row_3_1_0
  · exact assocABC_row_3_1_1
  · exact assocABC_row_3_1_2
  · exact assocABC_row_3_1_3

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425919,
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

def outerABC : Matrix (LeftIndex 3 6 3) (RightIndex 3 3 6) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 3 6 3 r) []).getD (rightPosition 3 3 6 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 3 6 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_1_0
  · exact outerABC_row_2_1_1
  · exact outerABC_row_2_1_2
  · exact outerABC_row_2_1_3
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_1_0
  · exact outerABC_row_3_1_1
  · exact outerABC_row_3_1_2
  · exact outerABC_row_3_1_3

def assocBAC : Matrix (RightIndex 3 3 6) (LeftIndex 3 3 6) ℤ := assocABC

theorem assocBAC_eq : associatorZ 3 3 6 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 927639642511048,
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

def innerABC : Matrix (LeftIndex 3 3 6) (LeftIndex 3 3 6) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 3 3 6 r) []).getD (leftPosition 3 3 6 s) 0

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_2 : (innerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_3 : (innerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_2 : (innerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_3 : (innerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 3 6 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_1_2
  · exact innerABC_row_0_1_3
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_1_0
  · exact innerABC_row_2_1_1
  · exact innerABC_row_2_1_2
  · exact innerABC_row_2_1_3
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_1_0
  · exact innerABC_row_3_1_1
  · exact innerABC_row_3_1_2
  · exact innerABC_row_3_1_3

def innerRightABC : Matrix (RightIndex 3 6 3) (RightIndex 3 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_2 : (innerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_3 : (innerRightZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_2 : (innerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_3 : (innerRightZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 3 6 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_1_2
  · exact innerRightABC_row_0_1_3
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_1_2
  · exact innerRightABC_row_1_1_3
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_0_2
  · exact innerRightABC_row_2_0_3
  · exact innerRightABC_row_2_1_0
  · exact innerRightABC_row_2_1_1
  · exact innerRightABC_row_2_1_2
  · exact innerRightABC_row_2_1_3
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_0_2
  · exact innerRightABC_row_3_0_3
  · exact innerRightABC_row_3_1_0
  · exact innerRightABC_row_3_1_1
  · exact innerRightABC_row_3_1_2
  · exact innerRightABC_row_3_1_3

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 936676773335236,
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

def inverseACB : Matrix (LeftIndex 3 6 3) (RightIndex 3 6 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 6 3 r) []).getD (rightPosition 3 6 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_2 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_3 : (associatorInverseZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_2 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_3 : (associatorInverseZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 6 3 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_1_2
  · exact inverseACB_row_0_1_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_1_0
  · exact inverseACB_row_2_1_1
  · exact inverseACB_row_2_1_2
  · exact inverseACB_row_2_1_3
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_1_0
  · exact inverseACB_row_3_1_1
  · exact inverseACB_row_3_1_2
  · exact inverseACB_row_3_1_3

def innerACB : Matrix (LeftIndex 6 3 3) (LeftIndex 3 6 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_2 : (innerLeftZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_3 : (innerLeftZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_2 : (innerLeftZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_3 : (innerLeftZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_0 : (innerLeftZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_1 : (innerLeftZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_2 : (innerLeftZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_3 : (innerLeftZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_0 : (innerLeftZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_1 : (innerLeftZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_2 : (innerLeftZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_3 : (innerLeftZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 6 3 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_0_1_0
  · exact innerACB_row_0_1_1
  · exact innerACB_row_0_1_2
  · exact innerACB_row_0_1_3
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_1_0
  · exact innerACB_row_1_1_1
  · exact innerACB_row_1_1_2
  · exact innerACB_row_1_1_3
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_2_1_0
  · exact innerACB_row_2_1_1
  · exact innerACB_row_2_1_2
  · exact innerACB_row_2_1_3
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_3_1_0
  · exact innerACB_row_3_1_1
  · exact innerACB_row_3_1_2
  · exact innerACB_row_3_1_3

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 916343396390560,
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

def assocBCA : Matrix (RightIndex 3 6 3) (LeftIndex 3 6 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 3 6 3 r) []).getD (leftPosition 3 6 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 3 6 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_0 : (associatorZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_1 : (associatorZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_2 : (associatorZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_3 : (associatorZ 3 6 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 3 6 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_0 : (associatorZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_1 : (associatorZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_2 : (associatorZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_3 : (associatorZ 3 6 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 3 6 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_0 : (associatorZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_1 : (associatorZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_2 : (associatorZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_3 : (associatorZ 3 6 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 3 6 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocBCA ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_0 : (associatorZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_1 : (associatorZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_2 : (associatorZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_3 : (associatorZ 3 6 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocBCA ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 3 6 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_0_1_0
  · exact assocBCA_row_0_1_1
  · exact assocBCA_row_0_1_2
  · exact assocBCA_row_0_1_3
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_1_0
  · exact assocBCA_row_1_1_1
  · exact assocBCA_row_1_1_2
  · exact assocBCA_row_1_1_3
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_2_1_0
  · exact assocBCA_row_2_1_1
  · exact assocBCA_row_2_1_2
  · exact assocBCA_row_2_1_3
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_3_1_0
  · exact assocBCA_row_3_1_1
  · exact assocBCA_row_3_1_2
  · exact assocBCA_row_3_1_3

def innerRightBAC : Matrix (RightIndex 3 6 3) (RightIndex 3 3 6) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 3 6 = innerRightBAC := innerRightABC_eq

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 925945417108696,
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

def assocCAB : Matrix (RightIndex 6 3 3) (LeftIndex 6 3 3) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 3 3 r) []).getD (leftPosition 6 3 3 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 6 3 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 6 3 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 6 3 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 6 3 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 6 3 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 6 3 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_2 : (associatorZ 6 3 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_3 : (associatorZ 6 3 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 6 3 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 6 3 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 6 3 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 6 3 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 6 3 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 6 3 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_2 : (associatorZ 6 3 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_3 : (associatorZ 6 3 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_0 : (associatorZ 6 3 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_1 : (associatorZ 6 3 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_2 : (associatorZ 6 3 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_3 : (associatorZ 6 3 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_0 : (associatorZ 6 3 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_1 : (associatorZ 6 3 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_2 : (associatorZ 6 3 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_3 : (associatorZ 6 3 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_0 : (associatorZ 6 3 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_1 : (associatorZ 6 3 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_2 : (associatorZ 6 3 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_3 : (associatorZ 6 3 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = assocCAB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_0 : (associatorZ 6 3 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_1 : (associatorZ 6 3 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_2 : (associatorZ 6 3 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_3 : (associatorZ 6 3 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = assocCAB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 6 3 3 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_0_2
  · exact assocCAB_row_0_0_3
  · exact assocCAB_row_0_1_0
  · exact assocCAB_row_0_1_1
  · exact assocCAB_row_0_1_2
  · exact assocCAB_row_0_1_3
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_1_0
  · exact assocCAB_row_1_1_1
  · exact assocCAB_row_1_1_2
  · exact assocCAB_row_1_1_3
  · exact assocCAB_row_2_0_0
  · exact assocCAB_row_2_0_1
  · exact assocCAB_row_2_0_2
  · exact assocCAB_row_2_0_3
  · exact assocCAB_row_2_1_0
  · exact assocCAB_row_2_1_1
  · exact assocCAB_row_2_1_2
  · exact assocCAB_row_2_1_3
  · exact assocCAB_row_3_0_0
  · exact assocCAB_row_3_0_1
  · exact assocCAB_row_3_0_2
  · exact assocCAB_row_3_0_3
  · exact assocCAB_row_3_1_0
  · exact assocCAB_row_3_1_1
  · exact assocCAB_row_3_1_2
  · exact assocCAB_row_3_1_3

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094445603,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094603067,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510108774827,
    decodeIntegerRow 32 3 1 926510099208889,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510051379199,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926509707005431,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926499634072717,
    decodeIntegerRow 32 3 1 926506607641519,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 926227664889439,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 923968228597591,
    decodeIntegerRow 32 3 1 1544183490709867,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 857879717061037,
    decodeIntegerRow 32 3 1 903633301970959]

def outerLeftABC : Matrix (RightIndex 6 3 3) (LeftIndex 3 3 6) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 6 3 3 r) []).getD (leftPosition 3 3 6 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 3 6) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 3 3 6) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 3 6) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 3 3 6) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 3 6) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 3 3 6) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 3 6) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 3 3 6) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 3 6 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_1_2
  · exact outerLeftABC_row_0_1_3
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_1_2
  · exact outerLeftABC_row_2_1_3
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_1_2
  · exact outerLeftABC_row_3_1_3

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms336
