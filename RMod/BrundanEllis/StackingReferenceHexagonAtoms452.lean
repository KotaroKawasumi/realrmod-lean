import RMod.BrundanEllis.StackingReferenceHexagonAtoms425
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms452
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1132087372405456,
    decodeIntegerRow 32 3 1 1543241931198340,
    decodeIntegerRow 32 3 1 946841151623340,
    decodeIntegerRow 32 3 1 987503237364112,
    decodeIntegerRow 32 3 1 901088341568976,
    decodeIntegerRow 32 3 1 850244807113540,
    decodeIntegerRow 32 3 1 720305194191340,
    decodeIntegerRow 32 3 1 307895397265552,
    decodeIntegerRow 32 3 1 1132714993479376,
    decodeIntegerRow 32 3 1 1545124795129660,
    decodeIntegerRow 32 3 1 951931856863380,
    decodeIntegerRow 32 3 1 1002775352996752,
    decodeIntegerRow 32 3 1 946841142071984,
    decodeIntegerRow 32 3 1 987503266018180,
    decodeIntegerRow 32 3 1 1132087373350060,
    decodeIntegerRow 32 3 1 1543241928364528,
    decodeIntegerRow 32 3 1 951925648556496,
    decodeIntegerRow 32 3 1 850263403301380,
    decodeIntegerRow 32 3 1 720367870217260,
    decodeIntegerRow 32 3 1 1544936763509392,
    decodeIntegerRow 32 3 1 1132150220617936,
    decodeIntegerRow 32 3 1 309589713014980,
    decodeIntegerRow 32 3 1 906171288817260,
    decodeIntegerRow 32 3 1 987526482589072,
    decodeIntegerRow 32 3 1 946848890480304,
    decodeIntegerRow 32 3 1 865493677599940,
    decodeIntegerRow 32 3 1 720869967288940,
    decodeIntegerRow 32 3 1 1543430473001968,
    decodeIntegerRow 32 3 1 720367871398096,
    decodeIntegerRow 32 3 1 1544936767051900,
    decodeIntegerRow 32 3 1 951925658134100,
    decodeIntegerRow 32 3 1 850263432034192]

def assocABC : Matrix (RightIndex 4 5 2) (LeftIndex 4 5 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 5 2 r) []).getD (leftPosition 4 5 2 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_4 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_5 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_6 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_7 : (associatorZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_4 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_5 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_6 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_7 : (associatorZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 4 5 2 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_0_2
  · exact assocABC_row_0_0_3
  · exact assocABC_row_0_0_4
  · exact assocABC_row_0_0_5
  · exact assocABC_row_0_0_6
  · exact assocABC_row_0_0_7
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_0_4
  · exact assocABC_row_1_0_5
  · exact assocABC_row_1_0_6
  · exact assocABC_row_1_0_7
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_0_2
  · exact assocABC_row_2_0_3
  · exact assocABC_row_2_0_4
  · exact assocABC_row_2_0_5
  · exact assocABC_row_2_0_6
  · exact assocABC_row_2_0_7
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_0_2
  · exact assocABC_row_3_0_3
  · exact assocABC_row_3_0_4
  · exact assocABC_row_3_0_5
  · exact assocABC_row_3_0_6
  · exact assocABC_row_3_0_7

def outerABC : Matrix (LeftIndex 5 2 4) (RightIndex 4 5 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 4 5 2 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_0_4
  · exact outerABC_row_0_0_5
  · exact outerABC_row_0_0_6
  · exact outerABC_row_0_0_7
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_0_4
  · exact outerABC_row_2_0_5
  · exact outerABC_row_2_0_6
  · exact outerABC_row_2_0_7
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_0_4
  · exact outerABC_row_3_0_5
  · exact outerABC_row_3_0_6
  · exact outerABC_row_3_0_7

def assocBAC : Matrix (RightIndex 5 4 2) (LeftIndex 5 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.assocCAB

theorem assocBAC_eq : associatorZ 5 4 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.assocCAB_eq

def innerABC : Matrix (LeftIndex 5 4 2) (LeftIndex 4 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.innerACB

theorem innerABC_eq : innerLeftZ 4 5 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 2 5) (RightIndex 4 5 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_4 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_5 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_6 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_7 : (innerRightZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_4 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_5 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_6 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_7 : (innerRightZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 4 5 2 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_0_0_4
  · exact innerRightABC_row_0_0_5
  · exact innerRightABC_row_0_0_6
  · exact innerRightABC_row_0_0_7
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_0_4
  · exact innerRightABC_row_1_0_5
  · exact innerRightABC_row_1_0_6
  · exact innerRightABC_row_1_0_7
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_0_2
  · exact innerRightABC_row_2_0_3
  · exact innerRightABC_row_2_0_4
  · exact innerRightABC_row_2_0_5
  · exact innerRightABC_row_2_0_6
  · exact innerRightABC_row_2_0_7
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_0_2
  · exact innerRightABC_row_3_0_3
  · exact innerRightABC_row_3_0_4
  · exact innerRightABC_row_3_0_5
  · exact innerRightABC_row_3_0_6
  · exact innerRightABC_row_3_0_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 720889769845756,
    decodeIntegerRow 32 3 1 309680110774328,
    decodeIntegerRow 32 3 1 906269435328964,
    decodeIntegerRow 32 3 1 865536753020872,
    decodeIntegerRow 32 3 1 951834743446684,
    decodeIntegerRow 32 3 1 1002734716933768,
    decodeIntegerRow 32 3 1 1132692953674204,
    decodeIntegerRow 32 3 1 1545033880101128,
    decodeIntegerRow 32 3 1 1545033877265316,
    decodeIntegerRow 32 3 1 720327234228472,
    decodeIntegerRow 32 3 1 1002734745592036,
    decodeIntegerRow 32 3 1 901185454957432,
    decodeIntegerRow 32 3 1 987483464568004,
    decodeIntegerRow 32 3 1 906269444907592,
    decodeIntegerRow 32 3 1 1543340074533116,
    decodeIntegerRow 32 3 1 720889768660408,
    decodeIntegerRow 32 3 1 309687862727048,
    decodeIntegerRow 32 3 1 1132107174957724,
    decodeIntegerRow 32 3 1 865473876071032,
    decodeIntegerRow 32 3 1 946939288581796,
    decodeIntegerRow 32 3 1 1002797421617992,
    decodeIntegerRow 32 3 1 900997426880644,
    decodeIntegerRow 32 3 1 1545027678538952,
    decodeIntegerRow 32 3 1 720345830416324,
    decodeIntegerRow 32 3 1 1132674357495112,
    decodeIntegerRow 32 3 1 1545027681371844,
    decodeIntegerRow 32 3 1 952022771524552,
    decodeIntegerRow 32 3 1 1002797392959364,
    decodeIntegerRow 32 3 1 946939298161288,
    decodeIntegerRow 32 3 1 987546284043484,
    decodeIntegerRow 32 3 1 1132107173781112,
    decodeIntegerRow 32 3 1 1543332329666276]

def inverseACB : Matrix (LeftIndex 4 2 5) (RightIndex 4 2 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 2 5 r) []).getD (rightPosition 4 2 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_4 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_5 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_6 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_7 : (associatorInverseZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_4 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_5 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_6 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_7 : (associatorInverseZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 4 2 5 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_0_4
  · exact inverseACB_row_0_0_5
  · exact inverseACB_row_0_0_6
  · exact inverseACB_row_0_0_7
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_1_2
  · exact inverseACB_row_0_1_3
  · exact inverseACB_row_0_1_4
  · exact inverseACB_row_0_1_5
  · exact inverseACB_row_0_1_6
  · exact inverseACB_row_0_1_7
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_0_4
  · exact inverseACB_row_1_0_5
  · exact inverseACB_row_1_0_6
  · exact inverseACB_row_1_0_7
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_1_1_4
  · exact inverseACB_row_1_1_5
  · exact inverseACB_row_1_1_6
  · exact inverseACB_row_1_1_7

def innerACB : Matrix (LeftIndex 2 4 5) (LeftIndex 4 2 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.innerABC

theorem innerACB_eq : innerLeftZ 4 2 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 1132130419006084,
    decodeIntegerRow 32 3 1 1543340078077512,
    decodeIntegerRow 32 3 1 946750753522876,
    decodeIntegerRow 32 3 1 987483435830968,
    decodeIntegerRow 32 3 1 901185445405156,
    decodeIntegerRow 32 3 1 850285471918072,
    decodeIntegerRow 32 3 1 720327235177636,
    decodeIntegerRow 32 3 1 307986308750712,
    decodeIntegerRow 32 3 1 307986311586524,
    decodeIntegerRow 32 3 1 1132692954623368,
    decodeIntegerRow 32 3 1 850285443259804,
    decodeIntegerRow 32 3 1 951834733894408,
    decodeIntegerRow 32 3 1 865536724283836,
    decodeIntegerRow 32 3 1 946750743944248,
    decodeIntegerRow 32 3 1 309680114318724,
    decodeIntegerRow 32 3 1 1132130420191432,
    decodeIntegerRow 32 3 1 1543332326124792,
    decodeIntegerRow 32 3 1 720913013894116,
    decodeIntegerRow 32 3 1 987546312780808,
    decodeIntegerRow 32 3 1 906080900270044,
    decodeIntegerRow 32 3 1 850222767233848,
    decodeIntegerRow 32 3 1 952022761971196,
    decodeIntegerRow 32 3 1 307992510312888,
    decodeIntegerRow 32 3 1 1132674358435516,
    decodeIntegerRow 32 3 1 720345831356728,
    decodeIntegerRow 32 3 1 307992507479996,
    decodeIntegerRow 32 3 1 900997417327288,
    decodeIntegerRow 32 3 1 850222795892476,
    decodeIntegerRow 32 3 1 906080890690552,
    decodeIntegerRow 32 3 1 865473904808356,
    decodeIntegerRow 32 3 1 720913015070728,
    decodeIntegerRow 32 3 1 309687859185564]

def assocBCA : Matrix (RightIndex 5 2 4) (LeftIndex 5 2 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 2 4 r) []).getD (leftPosition 5 2 4 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 5 2 4) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocBCA ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_0 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_1 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_2 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_3 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_4 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_5 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_6 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_7 : (associatorZ 5 2 4) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocBCA ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 5 2 4) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocBCA ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_0 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_1 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_2 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_3 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_4 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_5 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_6 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_7 : (associatorZ 5 2 4) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocBCA ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 5 2 4 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_0_2
  · exact assocBCA_row_0_0_3
  · exact assocBCA_row_0_0_4
  · exact assocBCA_row_0_0_5
  · exact assocBCA_row_0_0_6
  · exact assocBCA_row_0_0_7
  · exact assocBCA_row_0_1_0
  · exact assocBCA_row_0_1_1
  · exact assocBCA_row_0_1_2
  · exact assocBCA_row_0_1_3
  · exact assocBCA_row_0_1_4
  · exact assocBCA_row_0_1_5
  · exact assocBCA_row_0_1_6
  · exact assocBCA_row_0_1_7
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_0_4
  · exact assocBCA_row_1_0_5
  · exact assocBCA_row_1_0_6
  · exact assocBCA_row_1_0_7
  · exact assocBCA_row_1_1_0
  · exact assocBCA_row_1_1_1
  · exact assocBCA_row_1_1_2
  · exact assocBCA_row_1_1_3
  · exact assocBCA_row_1_1_4
  · exact assocBCA_row_1_1_5
  · exact assocBCA_row_1_1_6
  · exact assocBCA_row_1_1_7

def innerRightBAC : Matrix (RightIndex 5 2 4) (RightIndex 5 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightBAC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_0 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_1 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_2 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_3 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_4 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_5 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_6 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_7 : (innerRightZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightBAC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightBAC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_0 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_1 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_2 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_3 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_4 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_5 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_6 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_7 : (innerRightZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightBAC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 5 4 2 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_0_0_4
  · exact innerRightBAC_row_0_0_5
  · exact innerRightBAC_row_0_0_6
  · exact innerRightBAC_row_0_0_7
  · exact innerRightBAC_row_0_1_0
  · exact innerRightBAC_row_0_1_1
  · exact innerRightBAC_row_0_1_2
  · exact innerRightBAC_row_0_1_3
  · exact innerRightBAC_row_0_1_4
  · exact innerRightBAC_row_0_1_5
  · exact innerRightBAC_row_0_1_6
  · exact innerRightBAC_row_0_1_7
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_0_4
  · exact innerRightBAC_row_1_0_5
  · exact innerRightBAC_row_1_0_6
  · exact innerRightBAC_row_1_0_7
  · exact innerRightBAC_row_1_1_0
  · exact innerRightBAC_row_1_1_1
  · exact innerRightBAC_row_1_1_2
  · exact innerRightBAC_row_1_1_3
  · exact innerRightBAC_row_1_1_4
  · exact innerRightBAC_row_1_1_5
  · exact innerRightBAC_row_1_1_6
  · exact innerRightBAC_row_1_1_7

def assocCAB : Matrix (RightIndex 2 4 5) (LeftIndex 2 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.assocBAC

theorem assocCAB_eq : associatorZ 2 4 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094426434,
    decodeIntegerRow 32 3 1 926510094428038,
    decodeIntegerRow 32 3 1 926510094428194,
    decodeIntegerRow 32 3 1 926510094426918,
    decodeIntegerRow 32 3 1 926510094428182,
    decodeIntegerRow 32 3 1 926510094426866,
    decodeIntegerRow 32 3 1 926510094426378,
    decodeIntegerRow 32 3 1 926510094428014,
    decodeIntegerRow 32 3 1 926510097798274,
    decodeIntegerRow 32 3 1 926510108322118,
    decodeIntegerRow 32 3 1 926510109345634,
    decodeIntegerRow 32 3 1 926510100973798,
    decodeIntegerRow 32 3 1 926510109266902,
    decodeIntegerRow 32 3 1 926510100632626,
    decodeIntegerRow 32 3 1 926510097430858,
    decodeIntegerRow 32 3 1 926510108164654,
    decodeIntegerRow 32 3 1 926532220440514,
    decodeIntegerRow 32 3 1 926601267380998,
    decodeIntegerRow 32 3 1 926607982669474,
    decodeIntegerRow 32 3 1 926553055053478,
    decodeIntegerRow 32 3 1 926607466108822,
    decodeIntegerRow 32 3 1 926550816623986,
    decodeIntegerRow 32 3 1 926529809824138,
    decodeIntegerRow 32 3 1 926600234259694,
    decodeIntegerRow 32 3 1 1071678876177154,
    decodeIntegerRow 32 3 1 1524695852692678,
    decodeIntegerRow 32 3 1 1568754860383714,
    decodeIntegerRow 32 3 1 1208374771833958,
    decodeIntegerRow 32 3 1 1565365705945942,
    decodeIntegerRow 32 3 1 1193688435936946,
    decodeIntegerRow 32 3 1 1055862822134218,
    decodeIntegerRow 32 3 1 1517917543817134]

def outerLeftABC : Matrix (RightIndex 2 4 5) (LeftIndex 4 5 2) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 2 4 5 r) []).getD (leftPosition 4 5 2 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 4 5 2 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_0_4
  · exact outerLeftABC_row_0_0_5
  · exact outerLeftABC_row_0_0_6
  · exact outerLeftABC_row_0_0_7
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_0_4
  · exact outerLeftABC_row_1_0_5
  · exact outerLeftABC_row_1_0_6
  · exact outerLeftABC_row_1_0_7
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_0_4
  · exact outerLeftABC_row_2_0_5
  · exact outerLeftABC_row_2_0_6
  · exact outerLeftABC_row_2_0_7
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_0_4
  · exact outerLeftABC_row_3_0_5
  · exact outerLeftABC_row_3_0_6
  · exact outerLeftABC_row_3_0_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms452
