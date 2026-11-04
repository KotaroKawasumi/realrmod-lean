import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1543367630985352,
    decodeIntegerRow 32 3 1 720995678515236,
    decodeIntegerRow 32 3 1 987518748983368,
    decodeIntegerRow 32 3 1 906186791831044,
    decodeIntegerRow 32 3 1 850257218349688,
    decodeIntegerRow 32 3 1 951938049029404,
    decodeIntegerRow 32 3 1 308020742758072,
    decodeIntegerRow 32 3 1 1132777655726396,
    decodeIntegerRow 32 3 1 946833399854968,
    decodeIntegerRow 32 3 1 865501440813796,
    decodeIntegerRow 32 3 1 720995649858248,
    decodeIntegerRow 32 3 1 1543367621428156,
    decodeIntegerRow 32 3 1 720242504386808,
    decodeIntegerRow 32 3 1 1544999436519076,
    decodeIntegerRow 32 3 1 951938052572488,
    decodeIntegerRow 32 3 1 850257219530236,
    decodeIntegerRow 32 3 1 987510999628804,
    decodeIntegerRow 32 3 1 946856645084488,
    decodeIntegerRow 32 3 1 309715415631964,
    decodeIntegerRow 32 3 1 720807105218808,
    decodeIntegerRow 32 3 1 307958076311356,
    decodeIntegerRow 32 3 1 720430532465592,
    decodeIntegerRow 32 3 1 1002769168048996,
    decodeIntegerRow 32 3 1 951919456388872,
    decodeIntegerRow 32 3 1 720807133878716,
    decodeIntegerRow 32 3 1 309715406083528,
    decodeIntegerRow 32 3 1 906163546601884,
    decodeIntegerRow 32 3 1 865509188278792,
    decodeIntegerRow 32 3 1 951919452846076,
    decodeIntegerRow 32 3 1 1002769169230408,
    decodeIntegerRow 32 3 1 1132589627650524,
    decodeIntegerRow 32 3 1 1545062122123912]

def assocABC : Matrix (RightIndex 4 2 5) (LeftIndex 4 2 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 2 5 r) []).getD (leftPosition 4 2 5 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_2 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_3 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_4 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_5 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_6 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_7 : (associatorZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_2 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_3 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_4 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_5 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_6 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_7 : (associatorZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 4 2 5 = assocABC := by
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

def outerABC : Matrix (LeftIndex 2 5 4) (RightIndex 4 2 5) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 4 2 5 = outerABC := by
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

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926792394763216,
    decodeIntegerRow 32 3 1 927357426259240,
    decodeIntegerRow 32 3 1 929050797999340,
    decodeIntegerRow 32 3 1 934136079311712,
    decodeIntegerRow 32 3 1 949376421746896,
    decodeIntegerRow 32 3 1 995143972924840,
    decodeIntegerRow 32 3 1 1132307083872940,
    decodeIntegerRow 32 3 1 1544214870175072,
    decodeIntegerRow 32 3 1 995136999354580,
    decodeIntegerRow 32 3 1 949397342448928,
    decodeIntegerRow 32 3 1 308868080795824,
    decodeIntegerRow 32 3 1 720524818620760,
    decodeIntegerRow 32 3 1 925662848686060,
    decodeIntegerRow 32 3 1 926227535808352,
    decodeIntegerRow 32 3 1 934135304470736,
    decodeIntegerRow 32 3 1 929053122522280,
    decodeIntegerRow 32 3 1 1544214873363880,
    decodeIntegerRow 32 3 1 720713106041296,
    decodeIntegerRow 32 3 1 995143944225568,
    decodeIntegerRow 32 3 1 903643757543380,
    decodeIntegerRow 32 3 1 918884109500760,
    decodeIntegerRow 32 3 1 929050797986224,
    decodeIntegerRow 32 3 1 925662762946912,
    decodeIntegerRow 32 3 1 926792394881260,
    decodeIntegerRow 32 3 1 929053122509152,
    decodeIntegerRow 32 3 1 918884884341740,
    decodeIntegerRow 32 3 1 926227535690200,
    decodeIntegerRow 32 3 1 927357339811504,
    decodeIntegerRow 32 3 1 1132495369167712,
    decodeIntegerRow 32 3 1 308868077607340,
    decodeIntegerRow 32 3 1 903622836832600,
    decodeIntegerRow 32 3 1 995136970658224]

def assocBAC : Matrix (RightIndex 2 4 5) (LeftIndex 2 4 5) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 4 5 r) []).getD (leftPosition 2 4 5 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_4 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_5 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_6 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_7 : (associatorZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_4 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_5 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_6 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_7 : (associatorZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_4 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_5 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_6 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_7 : (associatorZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_4 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_5 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_6 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_7 : (associatorZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 2 4 5 = assocBAC := by
  funext r
  fin_cases r
  · exact assocBAC_row_0_0_0
  · exact assocBAC_row_0_0_1
  · exact assocBAC_row_0_0_2
  · exact assocBAC_row_0_0_3
  · exact assocBAC_row_0_0_4
  · exact assocBAC_row_0_0_5
  · exact assocBAC_row_0_0_6
  · exact assocBAC_row_0_0_7
  · exact assocBAC_row_1_0_0
  · exact assocBAC_row_1_0_1
  · exact assocBAC_row_1_0_2
  · exact assocBAC_row_1_0_3
  · exact assocBAC_row_1_0_4
  · exact assocBAC_row_1_0_5
  · exact assocBAC_row_1_0_6
  · exact assocBAC_row_1_0_7
  · exact assocBAC_row_2_0_0
  · exact assocBAC_row_2_0_1
  · exact assocBAC_row_2_0_2
  · exact assocBAC_row_2_0_3
  · exact assocBAC_row_2_0_4
  · exact assocBAC_row_2_0_5
  · exact assocBAC_row_2_0_6
  · exact assocBAC_row_2_0_7
  · exact assocBAC_row_3_0_0
  · exact assocBAC_row_3_0_1
  · exact assocBAC_row_3_0_2
  · exact assocBAC_row_3_0_3
  · exact assocBAC_row_3_0_4
  · exact assocBAC_row_3_0_5
  · exact assocBAC_row_3_0_6
  · exact assocBAC_row_3_0_7

def innerABC : Matrix (LeftIndex 2 4 5) (LeftIndex 4 2 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_4 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_5 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_6 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_7 : (innerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_4 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_5 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_6 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_7 : (innerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 4 2 5 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_0_4
  · exact innerABC_row_0_0_5
  · exact innerABC_row_0_0_6
  · exact innerABC_row_0_0_7
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_1_2
  · exact innerABC_row_0_1_3
  · exact innerABC_row_0_1_4
  · exact innerABC_row_0_1_5
  · exact innerABC_row_0_1_6
  · exact innerABC_row_0_1_7
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_0_4
  · exact innerABC_row_1_0_5
  · exact innerABC_row_1_0_6
  · exact innerABC_row_1_0_7
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_1_1_4
  · exact innerABC_row_1_1_5
  · exact innerABC_row_1_1_6
  · exact innerABC_row_1_1_7

def innerRightABC : Matrix (RightIndex 4 5 2) (RightIndex 4 2 5) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 4 2 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 4 2 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_4 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_5 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_6 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_7 : (innerRightZ 4 2 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_4 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_5 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_6 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_7 : (innerRightZ 4 2 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 4 2 5 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1132087373350060,
    decodeIntegerRow 32 3 1 1543241928364528,
    decodeIntegerRow 32 3 1 946841142071984,
    decodeIntegerRow 32 3 1 987503266018180,
    decodeIntegerRow 32 3 1 901088331988460,
    decodeIntegerRow 32 3 1 850244835855088,
    decodeIntegerRow 32 3 1 720305195372464,
    decodeIntegerRow 32 3 1 307895393722180,
    decodeIntegerRow 32 3 1 1132714994660500,
    decodeIntegerRow 32 3 1 1545124791586288,
    decodeIntegerRow 32 3 1 951931847282864,
    decodeIntegerRow 32 3 1 1002775381738300,
    decodeIntegerRow 32 3 1 946841151623340,
    decodeIntegerRow 32 3 1 987503237364112,
    decodeIntegerRow 32 3 1 1132087372405456,
    decodeIntegerRow 32 3 1 1543241931198340,
    decodeIntegerRow 32 3 1 901094530717740,
    decodeIntegerRow 32 3 1 1002756756817648,
    decodeIntegerRow 32 3 1 1132652317453744,
    decodeIntegerRow 32 3 1 308083421799940,
    decodeIntegerRow 32 3 1 720869967288940,
    decodeIntegerRow 32 3 1 1543430473001968,
    decodeIntegerRow 32 3 1 946848890480304,
    decodeIntegerRow 32 3 1 865493677599940,
    decodeIntegerRow 32 3 1 906171288817260,
    decodeIntegerRow 32 3 1 987526482589072,
    decodeIntegerRow 32 3 1 1132150220617936,
    decodeIntegerRow 32 3 1 309589713014980,
    decodeIntegerRow 32 3 1 1132652318634580,
    decodeIntegerRow 32 3 1 308083425342448,
    decodeIntegerRow 32 3 1 901094540295344,
    decodeIntegerRow 32 3 1 1002756785550460]

def inverseACB : Matrix (LeftIndex 4 5 2) (RightIndex 4 5 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 5 2 r) []).getD (rightPosition 4 5 2 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 4 5 2 = inverseACB := by
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
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_0_4
  · exact inverseACB_row_1_0_5
  · exact inverseACB_row_1_0_6
  · exact inverseACB_row_1_0_7
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_0_4
  · exact inverseACB_row_2_0_5
  · exact inverseACB_row_2_0_6
  · exact inverseACB_row_2_0_7
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_0_4
  · exact inverseACB_row_3_0_5
  · exact inverseACB_row_3_0_6
  · exact inverseACB_row_3_0_7

def innerACB : Matrix (LeftIndex 5 4 2) (LeftIndex 4 5 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 4 5 2) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 4 5 2) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_4 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_5 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_6 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_7 : (innerLeftZ 4 5 2) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_4 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_5 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_6 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_7 : (innerLeftZ 4 5 2) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 4 5 2 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_0_0_4
  · exact innerACB_row_0_0_5
  · exact innerACB_row_0_0_6
  · exact innerACB_row_0_0_7
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_0_4
  · exact innerACB_row_1_0_5
  · exact innerACB_row_1_0_6
  · exact innerACB_row_1_0_7
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_2_0_4
  · exact innerACB_row_2_0_5
  · exact innerACB_row_2_0_6
  · exact innerACB_row_2_0_7
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_3_0_4
  · exact innerACB_row_3_0_5
  · exact innerACB_row_3_0_6
  · exact innerACB_row_3_0_7

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 858194689409032,
    decodeIntegerRow 32 3 1 904575122766724,
    decodeIntegerRow 32 3 1 1546728719142792,
    decodeIntegerRow 32 3 1 1140037226904004,
    decodeIntegerRow 32 3 1 950327932850248,
    decodeIntegerRow 32 3 1 995453119572124,
    decodeIntegerRow 32 3 1 1124765139925432,
    decodeIntegerRow 32 3 1 1541638004351396,
    decodeIntegerRow 32 3 1 712982933131768,
    decodeIntegerRow 32 3 1 306291479629764,
    decodeIntegerRow 32 3 1 904575119592712,
    decodeIntegerRow 32 3 1 858194690428156,
    decodeIntegerRow 32 3 1 311382175289288,
    decodeIntegerRow 32 3 1 728255077505956,
    decodeIntegerRow 32 3 1 995453120678728,
    decodeIntegerRow 32 3 1 950327929647076,
    decodeIntegerRow 32 3 1 1546722003853832,
    decodeIntegerRow 32 3 1 713003796560644,
    decodeIntegerRow 32 3 1 994890586089352,
    decodeIntegerRow 32 3 1 904386061569604,
    decodeIntegerRow 32 3 1 1124786146725448,
    decodeIntegerRow 32 3 1 311374952651804,
    decodeIntegerRow 32 3 1 902879767519672,
    decodeIntegerRow 32 3 1 995392681980196,
    decodeIntegerRow 32 3 1 948634130459272,
    decodeIntegerRow 32 3 1 858129603790396,
    decodeIntegerRow 32 3 1 713003767744888,
    decodeIntegerRow 32 3 1 1546721993934084,
    decodeIntegerRow 32 3 1 857627505773752,
    decodeIntegerRow 32 3 1 950140418131804,
    decodeIntegerRow 32 3 1 311374943439672,
    decodeIntegerRow 32 3 1 1124786118145564]

def assocBCA : Matrix (RightIndex 2 5 4) (LeftIndex 2 5 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 5 4 r) []).getD (leftPosition 2 5 4 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 2 5 4) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 2 5 4) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_4 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_5 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_6 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_7 : (associatorZ 2 5 4) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_4 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_5 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_6 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_7 : (associatorZ 2 5 4) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 2 5 4 = assocBCA := by
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
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_0_2
  · exact assocBCA_row_1_0_3
  · exact assocBCA_row_1_0_4
  · exact assocBCA_row_1_0_5
  · exact assocBCA_row_1_0_6
  · exact assocBCA_row_1_0_7
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_0_2
  · exact assocBCA_row_2_0_3
  · exact assocBCA_row_2_0_4
  · exact assocBCA_row_2_0_5
  · exact assocBCA_row_2_0_6
  · exact assocBCA_row_2_0_7
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_0_2
  · exact assocBCA_row_3_0_3
  · exact assocBCA_row_3_0_4
  · exact assocBCA_row_3_0_5
  · exact assocBCA_row_3_0_6
  · exact assocBCA_row_3_0_7

def innerRightBAC : Matrix (RightIndex 2 5 4) (RightIndex 2 4 5) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 2 4 5) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 2 4 5) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 2 4 5) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 2 4 5) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 2 4 5 = innerRightBAC := by
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
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_0_4
  · exact innerRightBAC_row_1_0_5
  · exact innerRightBAC_row_1_0_6
  · exact innerRightBAC_row_1_0_7
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_2_0_4
  · exact innerRightBAC_row_2_0_5
  · exact innerRightBAC_row_2_0_6
  · exact innerRightBAC_row_2_0_7
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_3_0_4
  · exact innerRightBAC_row_3_0_5
  · exact innerRightBAC_row_3_0_6
  · exact innerRightBAC_row_3_0_7

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1524598484013716,
    decodeIntegerRow 32 3 1 781382048609212,
    decodeIntegerRow 32 3 1 1208394502075276,
    decodeIntegerRow 32 3 1 284175194841572,
    decodeIntegerRow 32 3 1 1193710547029732,
    decodeIntegerRow 32 3 1 287563303402484,
    decodeIntegerRow 32 3 1 1517819652202172,
    decodeIntegerRow 32 3 1 797200313451244,
    decodeIntegerRow 32 3 1 781300604217628,
    decodeIntegerRow 32 3 1 328226961470324,
    decodeIntegerRow 32 3 1 284355474508092,
    decodeIntegerRow 32 3 1 644665117577236,
    decodeIntegerRow 32 3 1 287745649313556,
    decodeIntegerRow 32 3 1 659353893847108,
    decodeIntegerRow 32 3 1 797114392191604,
    decodeIntegerRow 32 3 1 335004760164452,
    decodeIntegerRow 32 3 1 644625716462764,
    decodeIntegerRow 32 3 1 284175182427132,
    decodeIntegerRow 32 3 1 1524598478005836,
    decodeIntegerRow 32 3 1 1071638167715548,
    decodeIntegerRow 32 3 1 335200529906852,
    decodeIntegerRow 32 3 1 797200341239116,
    decodeIntegerRow 32 3 1 1193710576873348,
    decodeIntegerRow 32 3 1 1565456872352684,
    decodeIntegerRow 32 3 1 284355462095708,
    decodeIntegerRow 32 3 1 1208355041596876,
    decodeIntegerRow 32 3 1 1071719612116228,
    decodeIntegerRow 32 3 1 328226967482196,
    decodeIntegerRow 32 3 1 797114419988524,
    decodeIntegerRow 32 3 1 1518015435433988,
    decodeIntegerRow 32 3 1 1565274526443444,
    decodeIntegerRow 32 3 1 659353864011868]

def assocCAB : Matrix (RightIndex 5 4 2) (LeftIndex 5 4 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 5 4 2 r) []).getD (leftPosition 5 4 2 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_4 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_5 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_6 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_7 : (associatorZ 5 4 2) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_2 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_3 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_4 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_5 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_6 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_7 : (associatorZ 5 4 2) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_4 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_5 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_6 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_7 : (associatorZ 5 4 2) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_2 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_3 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_4 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_5 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_6 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_7 : (associatorZ 5 4 2) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocCAB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 5 4 2 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_0_2
  · exact assocCAB_row_0_0_3
  · exact assocCAB_row_0_0_4
  · exact assocCAB_row_0_0_5
  · exact assocCAB_row_0_0_6
  · exact assocCAB_row_0_0_7
  · exact assocCAB_row_0_1_0
  · exact assocCAB_row_0_1_1
  · exact assocCAB_row_0_1_2
  · exact assocCAB_row_0_1_3
  · exact assocCAB_row_0_1_4
  · exact assocCAB_row_0_1_5
  · exact assocCAB_row_0_1_6
  · exact assocCAB_row_0_1_7
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_0_4
  · exact assocCAB_row_1_0_5
  · exact assocCAB_row_1_0_6
  · exact assocCAB_row_1_0_7
  · exact assocCAB_row_1_1_0
  · exact assocCAB_row_1_1_1
  · exact assocCAB_row_1_1_2
  · exact assocCAB_row_1_1_3
  · exact assocCAB_row_1_1_4
  · exact assocCAB_row_1_1_5
  · exact assocCAB_row_1_1_6
  · exact assocCAB_row_1_1_7

def outerLeftABC : Matrix (RightIndex 5 4 2) (LeftIndex 4 2 5) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 4 2 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_4 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_5 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_6 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_7 : (outerLeftZ 4 2 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 4 2 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_4 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_5 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_6 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_7 : (outerLeftZ 4 2 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 4 2 5 = outerLeftABC := by
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
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_1_2
  · exact outerLeftABC_row_0_1_3
  · exact outerLeftABC_row_0_1_4
  · exact outerLeftABC_row_0_1_5
  · exact outerLeftABC_row_0_1_6
  · exact outerLeftABC_row_0_1_7
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_0_4
  · exact outerLeftABC_row_1_0_5
  · exact outerLeftABC_row_1_0_6
  · exact outerLeftABC_row_1_0_7
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_1_1_4
  · exact outerLeftABC_row_1_1_5
  · exact outerLeftABC_row_1_1_6
  · exact outerLeftABC_row_1_1_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms425
