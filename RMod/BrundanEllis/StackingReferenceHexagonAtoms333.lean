import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms333
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768960830324,
    decodeIntegerRow 32 3 1 1615533994468132,
    decodeIntegerRow 32 3 1 1116275897662428,
    decodeIntegerRow 32 3 1 1473209644343284,
    decodeIntegerRow 32 3 1 1477729206068236,
    decodeIntegerRow 32 3 1 750302975051868,
    decodeIntegerRow 32 3 1 243135645732772,
    decodeIntegerRow 32 3 1 1163717315927436,
    decodeIntegerRow 32 3 1 1102775068597836,
    decodeIntegerRow 32 3 1 1477895882970268,
    decodeIntegerRow 32 3 1 1163784468808292,
    decodeIntegerRow 32 3 1 1610094611118796,
    decodeIntegerRow 32 3 1 237277848252724,
    decodeIntegerRow 32 3 1 1146841279317732,
    decodeIntegerRow 32 3 1 1473377698740508,
    decodeIntegerRow 32 3 1 736690568876724,
    decodeIntegerRow 32 3 1 379642479087292,
    decodeIntegerRow 32 3 1 1116329588214996,
    decodeIntegerRow 32 3 1 237277856442196,
    decodeIntegerRow 32 3 1 1146841304935748,
    decodeIntegerRow 32 3 1 689235694635452,
    decodeIntegerRow 32 3 1 242925586552276,
    decodeIntegerRow 32 3 1 1102775036575316,
    decodeIntegerRow 32 3 1 1477895893207108,
    decodeIntegerRow 32 3 1 1609884534302332,
    decodeIntegerRow 32 3 1 689302847524116,
    decodeIntegerRow 32 3 1 1477729216301716,
    decodeIntegerRow 32 3 1 750303007064708,
    decodeIntegerRow 32 3 1 736744322939772,
    decodeIntegerRow 32 3 1 379810533487636,
    decodeIntegerRow 32 3 1 1146768986440596,
    decodeIntegerRow 32 3 1 1615533986281348]

def assocABC : Matrix (RightIndex 3 3 3) (LeftIndex 3 3 3) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 3 3 r) []).getD (leftPosition 3 3 3 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_0 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_2_1 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_0 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_3_1 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_0 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_2_1 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_0 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_3_1 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_0 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_0_1 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_0 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_1_1 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_2_0 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_2_1 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_3_0 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_2_3_1 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_0 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_0_1 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_0 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_1_1 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_2_0 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_2_1 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_3_0 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_3_3_1 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 3 3 = assocABC := by
  funext r
  fin_cases r
  · exact assocABC_row_0_0_0
  · exact assocABC_row_0_0_1
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_2_0
  · exact assocABC_row_0_2_1
  · exact assocABC_row_0_3_0
  · exact assocABC_row_0_3_1
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_2_0
  · exact assocABC_row_1_2_1
  · exact assocABC_row_1_3_0
  · exact assocABC_row_1_3_1
  · exact assocABC_row_2_0_0
  · exact assocABC_row_2_0_1
  · exact assocABC_row_2_1_0
  · exact assocABC_row_2_1_1
  · exact assocABC_row_2_2_0
  · exact assocABC_row_2_2_1
  · exact assocABC_row_2_3_0
  · exact assocABC_row_2_3_1
  · exact assocABC_row_3_0_0
  · exact assocABC_row_3_0_1
  · exact assocABC_row_3_1_0
  · exact assocABC_row_3_1_1
  · exact assocABC_row_3_2_0
  · exact assocABC_row_3_2_1
  · exact assocABC_row_3_3_0
  · exact assocABC_row_3_3_1

def outerABC : Matrix (LeftIndex 3 3 3) (RightIndex 3 3 3) ℤ :=
  (show Matrix (Fin 4 × Fin 4 × Fin 2) (Fin 4 × Fin 4 × Fin 2) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_0 : (outerRightZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_2_1 : (outerRightZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_0 : (outerRightZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_3_1 : (outerRightZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_0 : (outerRightZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_2_1 : (outerRightZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_0 : (outerRightZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_3_1 : (outerRightZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_2_0 : (outerRightZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_2_1 : (outerRightZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_3_0 : (outerRightZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_3_1 : (outerRightZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_2_0 : (outerRightZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_2_1 : (outerRightZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_3_0 : (outerRightZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_3_1 : (outerRightZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 3 3 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_2_0
  · exact outerABC_row_0_2_1
  · exact outerABC_row_0_3_0
  · exact outerABC_row_0_3_1
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_2_0
  · exact outerABC_row_1_2_1
  · exact outerABC_row_1_3_0
  · exact outerABC_row_1_3_1
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_1_0
  · exact outerABC_row_2_1_1
  · exact outerABC_row_2_2_0
  · exact outerABC_row_2_2_1
  · exact outerABC_row_2_3_0
  · exact outerABC_row_2_3_1
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_1_0
  · exact outerABC_row_3_1_1
  · exact outerABC_row_3_2_0
  · exact outerABC_row_3_2_1
  · exact outerABC_row_3_3_0
  · exact outerABC_row_3_3_1

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768960830324,
    decodeIntegerRow 32 3 1 1615533994468132,
    decodeIntegerRow 32 3 1 1116275897662428,
    decodeIntegerRow 32 3 1 1473209644343284,
    decodeIntegerRow 32 3 1 1477729206068236,
    decodeIntegerRow 32 3 1 750302975051868,
    decodeIntegerRow 32 3 1 243135645732772,
    decodeIntegerRow 32 3 1 1163717315927436,
    decodeIntegerRow 32 3 1 1102775068597836,
    decodeIntegerRow 32 3 1 1477895882970268,
    decodeIntegerRow 32 3 1 1163784468808292,
    decodeIntegerRow 32 3 1 1610094611118796,
    decodeIntegerRow 32 3 1 237277848252724,
    decodeIntegerRow 32 3 1 1146841279317732,
    decodeIntegerRow 32 3 1 1473377698740508,
    decodeIntegerRow 32 3 1 736690568876724,
    decodeIntegerRow 32 3 1 379642479087292,
    decodeIntegerRow 32 3 1 1116329588214996,
    decodeIntegerRow 32 3 1 237277856442196,
    decodeIntegerRow 32 3 1 1146841304935748,
    decodeIntegerRow 32 3 1 689235694635452,
    decodeIntegerRow 32 3 1 242925586552276,
    decodeIntegerRow 32 3 1 1102775036575316,
    decodeIntegerRow 32 3 1 1477895893207108,
    decodeIntegerRow 32 3 1 1609884534302332,
    decodeIntegerRow 32 3 1 689302847524116,
    decodeIntegerRow 32 3 1 1477729216301716,
    decodeIntegerRow 32 3 1 750303007064708,
    decodeIntegerRow 32 3 1 736744322939772,
    decodeIntegerRow 32 3 1 379810533487636,
    decodeIntegerRow 32 3 1 1146768986440596,
    decodeIntegerRow 32 3 1 1615533986281348]

def assocBAC : Matrix (RightIndex 3 3 3) (LeftIndex 3 3 3) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 3 3 3 r) []).getD (leftPosition 3 3 3 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBAC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBAC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_0 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBAC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_1_1 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBAC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_2_0 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBAC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_2_1 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBAC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_3_0 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBAC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_3_1 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBAC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBAC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBAC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_0 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBAC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_1_1 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBAC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_2_0 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBAC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_2_1 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBAC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_3_0 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBAC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_3_1 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBAC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBAC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBAC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_0 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBAC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_1_1 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBAC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_2_0 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBAC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_2_1 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBAC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_3_0 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBAC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_3_1 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBAC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBAC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBAC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_0 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBAC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_1_1 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBAC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_2_0 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBAC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_2_1 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBAC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_3_0 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBAC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_3_1 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBAC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 3 3 3 = assocBAC := by
  funext r
  fin_cases r
  · exact assocBAC_row_0_0_0
  · exact assocBAC_row_0_0_1
  · exact assocBAC_row_0_1_0
  · exact assocBAC_row_0_1_1
  · exact assocBAC_row_0_2_0
  · exact assocBAC_row_0_2_1
  · exact assocBAC_row_0_3_0
  · exact assocBAC_row_0_3_1
  · exact assocBAC_row_1_0_0
  · exact assocBAC_row_1_0_1
  · exact assocBAC_row_1_1_0
  · exact assocBAC_row_1_1_1
  · exact assocBAC_row_1_2_0
  · exact assocBAC_row_1_2_1
  · exact assocBAC_row_1_3_0
  · exact assocBAC_row_1_3_1
  · exact assocBAC_row_2_0_0
  · exact assocBAC_row_2_0_1
  · exact assocBAC_row_2_1_0
  · exact assocBAC_row_2_1_1
  · exact assocBAC_row_2_2_0
  · exact assocBAC_row_2_2_1
  · exact assocBAC_row_2_3_0
  · exact assocBAC_row_2_3_1
  · exact assocBAC_row_3_0_0
  · exact assocBAC_row_3_0_1
  · exact assocBAC_row_3_1_0
  · exact assocBAC_row_3_1_1
  · exact assocBAC_row_3_2_0
  · exact assocBAC_row_3_2_1
  · exact assocBAC_row_3_3_0
  · exact assocBAC_row_3_3_1

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929333963575696,
    decodeIntegerRow 32 3 1 934981701875248,
    decodeIntegerRow 32 3 1 928769191659220,
    decodeIntegerRow 32 3 1 933287386125820,
    decodeIntegerRow 32 3 1 1155243151184016,
    decodeIntegerRow 32 3 1 1612709264700208,
    decodeIntegerRow 32 3 1 1109496539856020,
    decodeIntegerRow 32 3 1 1475469430716220,
    decodeIntegerRow 32 3 1 923686233780496,
    decodeIntegerRow 32 3 1 918038512489648,
    decodeIntegerRow 32 3 1 924251007823060,
    decodeIntegerRow 32 3 1 919732834617340,
    decodeIntegerRow 32 3 1 697777037772816,
    decodeIntegerRow 32 3 1 240310924466608,
    decodeIntegerRow 32 3 1 743523649127060,
    decodeIntegerRow 32 3 1 377550758529340,
    decodeIntegerRow 32 3 1 697707301979820,
    decodeIntegerRow 32 3 1 240101717087620,
    decodeIntegerRow 32 3 1 1109552328406416,
    decodeIntegerRow 32 3 1 1475636796367408,
    decodeIntegerRow 32 3 1 923685364343020,
    decodeIntegerRow 32 3 1 918035904177220,
    decodeIntegerRow 32 3 1 928769880405136,
    decodeIntegerRow 32 3 1 933289452363568,
    decodeIntegerRow 32 3 1 697707302084780,
    decodeIntegerRow 32 3 1 240101717402500,
    decodeIntegerRow 32 3 1 1109552328275216,
    decodeIntegerRow 32 3 1 1475636795973808,
    decodeIntegerRow 32 3 1 923685372844780,
    decodeIntegerRow 32 3 1 918035929682500,
    decodeIntegerRow 32 3 1 928769869777936,
    decodeIntegerRow 32 3 1 933289420481968]

def innerABC : Matrix (LeftIndex 3 3 3) (LeftIndex 3 3 3) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 3 3 3 r) []).getD (leftPosition 3 3 3 s) 0

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_2_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_3_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_2_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_3_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_2_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_2_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_3_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_3_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_2_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_2_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_3_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_3_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 3 3 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_2_0
  · exact innerABC_row_0_2_1
  · exact innerABC_row_0_3_0
  · exact innerABC_row_0_3_1
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_2_0
  · exact innerABC_row_1_2_1
  · exact innerABC_row_1_3_0
  · exact innerABC_row_1_3_1
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_1_0
  · exact innerABC_row_2_1_1
  · exact innerABC_row_2_2_0
  · exact innerABC_row_2_2_1
  · exact innerABC_row_2_3_0
  · exact innerABC_row_2_3_1
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_1_0
  · exact innerABC_row_3_1_1
  · exact innerABC_row_3_2_0
  · exact innerABC_row_3_2_1
  · exact innerABC_row_3_3_0
  · exact innerABC_row_3_3_1

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929333963575696,
    decodeIntegerRow 32 3 1 934981701875248,
    decodeIntegerRow 32 3 1 928769191659220,
    decodeIntegerRow 32 3 1 933287386125820,
    decodeIntegerRow 32 3 1 1155243151184016,
    decodeIntegerRow 32 3 1 1612709264700208,
    decodeIntegerRow 32 3 1 1109496539856020,
    decodeIntegerRow 32 3 1 1475469430716220,
    decodeIntegerRow 32 3 1 923686233780496,
    decodeIntegerRow 32 3 1 918038512489648,
    decodeIntegerRow 32 3 1 924251007823060,
    decodeIntegerRow 32 3 1 919732834617340,
    decodeIntegerRow 32 3 1 697777037772816,
    decodeIntegerRow 32 3 1 240310924466608,
    decodeIntegerRow 32 3 1 743523649127060,
    decodeIntegerRow 32 3 1 377550758529340,
    decodeIntegerRow 32 3 1 697707301979820,
    decodeIntegerRow 32 3 1 240101717087620,
    decodeIntegerRow 32 3 1 1109552328406416,
    decodeIntegerRow 32 3 1 1475636796367408,
    decodeIntegerRow 32 3 1 923685364343020,
    decodeIntegerRow 32 3 1 918035904177220,
    decodeIntegerRow 32 3 1 928769880405136,
    decodeIntegerRow 32 3 1 933289452363568,
    decodeIntegerRow 32 3 1 697707302084780,
    decodeIntegerRow 32 3 1 240101717402500,
    decodeIntegerRow 32 3 1 1109552328275216,
    decodeIntegerRow 32 3 1 1475636795973808,
    decodeIntegerRow 32 3 1 923685372844780,
    decodeIntegerRow 32 3 1 918035929682500,
    decodeIntegerRow 32 3 1 928769869777936,
    decodeIntegerRow 32 3 1 933289420481968]

def innerRightABC : Matrix (RightIndex 3 3 3) (RightIndex 3 3 3) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 3 3 3 r) []).getD (rightPosition 3 3 3 s) 0

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_2_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_3_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_2_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_3_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_1_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_2_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_2_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_3_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_3_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_1_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_2_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_2_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_3_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_3_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 3 3 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_2_0
  · exact innerRightABC_row_0_2_1
  · exact innerRightABC_row_0_3_0
  · exact innerRightABC_row_0_3_1
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_2_0
  · exact innerRightABC_row_1_2_1
  · exact innerRightABC_row_1_3_0
  · exact innerRightABC_row_1_3_1
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_1_0
  · exact innerRightABC_row_2_1_1
  · exact innerRightABC_row_2_2_0
  · exact innerRightABC_row_2_2_1
  · exact innerRightABC_row_2_3_0
  · exact innerRightABC_row_2_3_1
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_1_0
  · exact innerRightABC_row_3_1_1
  · exact innerRightABC_row_3_2_0
  · exact innerRightABC_row_3_2_1
  · exact innerRightABC_row_3_3_0
  · exact innerRightABC_row_3_3_1

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 704556363823988,
    decodeIntegerRow 32 3 1 238051149116164,
    decodeIntegerRow 32 3 1 1118023910215356,
    decodeIntegerRow 32 3 1 1472812935327028,
    decodeIntegerRow 32 3 1 374726028051484,
    decodeIntegerRow 32 3 1 1101022349603412,
    decodeIntegerRow 32 3 1 1610659374532588,
    decodeIntegerRow 32 3 1 690930010284764,
    decodeIntegerRow 32 3 1 704484593674844,
    decodeIntegerRow 32 3 1 237842619855892,
    decodeIntegerRow 32 3 1 1117970730108588,
    decodeIntegerRow 32 3 1 1472644700631964,
    decodeIntegerRow 32 3 1 1478460656620468,
    decodeIntegerRow 32 3 1 751939442516804,
    decodeIntegerRow 32 3 1 242570699816956,
    decodeIntegerRow 32 3 1 1162022477130228,
    decodeIntegerRow 32 3 1 1472812927218988,
    decodeIntegerRow 32 3 1 734996252999964,
    decodeIntegerRow 32 3 1 1614969050680996,
    decodeIntegerRow 32 3 1 704556395610348,
    decodeIntegerRow 32 3 1 690930042271356,
    decodeIntegerRow 32 3 1 242360804007028,
    decodeIntegerRow 32 3 1 751997813866572,
    decodeIntegerRow 32 3 1 374726036949436,
    decodeIntegerRow 32 3 1 1472644708742716,
    decodeIntegerRow 32 3 1 735049484387508,
    decodeIntegerRow 32 3 1 1615177558053772,
    decodeIntegerRow 32 3 1 704484561898236,
    decodeIntegerRow 32 3 1 1162022509126508,
    decodeIntegerRow 32 3 1 1610449478719324,
    decodeIntegerRow 32 3 1 1101080720960996,
    decodeIntegerRow 32 3 1 1478460665515948]

def inverseACB : Matrix (LeftIndex 3 3 3) (RightIndex 3 3 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 3 3 r) []).getD (rightPosition 3 3 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_0 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_1 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_0 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_1 : (associatorInverseZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_0 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_1 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_0 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_1 : (associatorInverseZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_2_0 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_2_1 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_3_0 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_3_1 : (associatorInverseZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_2_0 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_2_1 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_3_0 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = inverseACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_3_1 : (associatorInverseZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = inverseACB ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 3 3 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_2_0
  · exact inverseACB_row_0_2_1
  · exact inverseACB_row_0_3_0
  · exact inverseACB_row_0_3_1
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_2_0
  · exact inverseACB_row_1_2_1
  · exact inverseACB_row_1_3_0
  · exact inverseACB_row_1_3_1
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_1_0
  · exact inverseACB_row_2_1_1
  · exact inverseACB_row_2_2_0
  · exact inverseACB_row_2_2_1
  · exact inverseACB_row_2_3_0
  · exact inverseACB_row_2_3_1
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_1_0
  · exact inverseACB_row_3_1_1
  · exact inverseACB_row_3_2_0
  · exact inverseACB_row_3_2_1
  · exact inverseACB_row_3_3_0
  · exact inverseACB_row_3_3_1

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929333963575696,
    decodeIntegerRow 32 3 1 934981701875248,
    decodeIntegerRow 32 3 1 928769191659220,
    decodeIntegerRow 32 3 1 933287386125820,
    decodeIntegerRow 32 3 1 1155243151184016,
    decodeIntegerRow 32 3 1 1612709264700208,
    decodeIntegerRow 32 3 1 1109496539856020,
    decodeIntegerRow 32 3 1 1475469430716220,
    decodeIntegerRow 32 3 1 923686233780496,
    decodeIntegerRow 32 3 1 918038512489648,
    decodeIntegerRow 32 3 1 924251007823060,
    decodeIntegerRow 32 3 1 919732834617340,
    decodeIntegerRow 32 3 1 697777037772816,
    decodeIntegerRow 32 3 1 240310924466608,
    decodeIntegerRow 32 3 1 743523649127060,
    decodeIntegerRow 32 3 1 377550758529340,
    decodeIntegerRow 32 3 1 697707301979820,
    decodeIntegerRow 32 3 1 240101717087620,
    decodeIntegerRow 32 3 1 1109552328406416,
    decodeIntegerRow 32 3 1 1475636796367408,
    decodeIntegerRow 32 3 1 923685364343020,
    decodeIntegerRow 32 3 1 918035904177220,
    decodeIntegerRow 32 3 1 928769880405136,
    decodeIntegerRow 32 3 1 933289452363568,
    decodeIntegerRow 32 3 1 697707302084780,
    decodeIntegerRow 32 3 1 240101717402500,
    decodeIntegerRow 32 3 1 1109552328275216,
    decodeIntegerRow 32 3 1 1475636795973808,
    decodeIntegerRow 32 3 1 923685372844780,
    decodeIntegerRow 32 3 1 918035929682500,
    decodeIntegerRow 32 3 1 928769869777936,
    decodeIntegerRow 32 3 1 933289420481968]

def innerACB : Matrix (LeftIndex 3 3 3) (LeftIndex 3 3 3) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 3 3 3 r) []).getD (leftPosition 3 3 3 s) 0

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerACB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerACB ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerACB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerACB ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_2_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerACB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_2_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerACB ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_3_0 : (innerLeftZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerACB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_3_1 : (innerLeftZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerACB ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerACB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerACB ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerACB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerACB ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_2_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerACB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_2_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerACB ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_3_0 : (innerLeftZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerACB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_3_1 : (innerLeftZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerACB ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerACB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerACB ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerACB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerACB ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_2_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerACB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_2_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerACB ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_3_0 : (innerLeftZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerACB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_3_1 : (innerLeftZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerACB ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerACB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerACB ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerACB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerACB ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_2_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerACB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_2_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerACB ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_3_0 : (innerLeftZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerACB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_3_1 : (innerLeftZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerACB ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 3 3 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_1_0
  · exact innerACB_row_0_1_1
  · exact innerACB_row_0_2_0
  · exact innerACB_row_0_2_1
  · exact innerACB_row_0_3_0
  · exact innerACB_row_0_3_1
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_1_0
  · exact innerACB_row_1_1_1
  · exact innerACB_row_1_2_0
  · exact innerACB_row_1_2_1
  · exact innerACB_row_1_3_0
  · exact innerACB_row_1_3_1
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_1_0
  · exact innerACB_row_2_1_1
  · exact innerACB_row_2_2_0
  · exact innerACB_row_2_2_1
  · exact innerACB_row_2_3_0
  · exact innerACB_row_2_3_1
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_1_0
  · exact innerACB_row_3_1_1
  · exact innerACB_row_3_2_0
  · exact innerACB_row_3_2_1
  · exact innerACB_row_3_3_0
  · exact innerACB_row_3_3_1

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768960830324,
    decodeIntegerRow 32 3 1 1615533994468132,
    decodeIntegerRow 32 3 1 1116275897662428,
    decodeIntegerRow 32 3 1 1473209644343284,
    decodeIntegerRow 32 3 1 1477729206068236,
    decodeIntegerRow 32 3 1 750302975051868,
    decodeIntegerRow 32 3 1 243135645732772,
    decodeIntegerRow 32 3 1 1163717315927436,
    decodeIntegerRow 32 3 1 1102775068597836,
    decodeIntegerRow 32 3 1 1477895882970268,
    decodeIntegerRow 32 3 1 1163784468808292,
    decodeIntegerRow 32 3 1 1610094611118796,
    decodeIntegerRow 32 3 1 237277848252724,
    decodeIntegerRow 32 3 1 1146841279317732,
    decodeIntegerRow 32 3 1 1473377698740508,
    decodeIntegerRow 32 3 1 736690568876724,
    decodeIntegerRow 32 3 1 379642479087292,
    decodeIntegerRow 32 3 1 1116329588214996,
    decodeIntegerRow 32 3 1 237277856442196,
    decodeIntegerRow 32 3 1 1146841304935748,
    decodeIntegerRow 32 3 1 689235694635452,
    decodeIntegerRow 32 3 1 242925586552276,
    decodeIntegerRow 32 3 1 1102775036575316,
    decodeIntegerRow 32 3 1 1477895893207108,
    decodeIntegerRow 32 3 1 1609884534302332,
    decodeIntegerRow 32 3 1 689302847524116,
    decodeIntegerRow 32 3 1 1477729216301716,
    decodeIntegerRow 32 3 1 750303007064708,
    decodeIntegerRow 32 3 1 736744322939772,
    decodeIntegerRow 32 3 1 379810533487636,
    decodeIntegerRow 32 3 1 1146768986440596,
    decodeIntegerRow 32 3 1 1615533986281348]

def assocBCA : Matrix (RightIndex 3 3 3) (LeftIndex 3 3 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 3 3 3 r) []).getD (leftPosition 3 3 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBCA ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBCA ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_0 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBCA ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_1_1 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBCA ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_2_0 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBCA ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_2_1 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBCA ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_3_0 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBCA ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_3_1 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBCA ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBCA ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBCA ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_0 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBCA ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_1_1 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBCA ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_2_0 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBCA ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_2_1 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBCA ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_3_0 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBCA ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_3_1 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBCA ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBCA ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBCA ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_0 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBCA ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_1_1 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBCA ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_2_0 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBCA ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_2_1 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBCA ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_3_0 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBCA ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_3_1 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBCA ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocBCA ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocBCA ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_0 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocBCA ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_1_1 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocBCA ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_2_0 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocBCA ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_2_1 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocBCA ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_3_0 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocBCA ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_3_1 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocBCA ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 3 3 3 = assocBCA := by
  funext r
  fin_cases r
  · exact assocBCA_row_0_0_0
  · exact assocBCA_row_0_0_1
  · exact assocBCA_row_0_1_0
  · exact assocBCA_row_0_1_1
  · exact assocBCA_row_0_2_0
  · exact assocBCA_row_0_2_1
  · exact assocBCA_row_0_3_0
  · exact assocBCA_row_0_3_1
  · exact assocBCA_row_1_0_0
  · exact assocBCA_row_1_0_1
  · exact assocBCA_row_1_1_0
  · exact assocBCA_row_1_1_1
  · exact assocBCA_row_1_2_0
  · exact assocBCA_row_1_2_1
  · exact assocBCA_row_1_3_0
  · exact assocBCA_row_1_3_1
  · exact assocBCA_row_2_0_0
  · exact assocBCA_row_2_0_1
  · exact assocBCA_row_2_1_0
  · exact assocBCA_row_2_1_1
  · exact assocBCA_row_2_2_0
  · exact assocBCA_row_2_2_1
  · exact assocBCA_row_2_3_0
  · exact assocBCA_row_2_3_1
  · exact assocBCA_row_3_0_0
  · exact assocBCA_row_3_0_1
  · exact assocBCA_row_3_1_0
  · exact assocBCA_row_3_1_1
  · exact assocBCA_row_3_2_0
  · exact assocBCA_row_3_2_1
  · exact assocBCA_row_3_3_0
  · exact assocBCA_row_3_3_1

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 929333963575696,
    decodeIntegerRow 32 3 1 934981701875248,
    decodeIntegerRow 32 3 1 928769191659220,
    decodeIntegerRow 32 3 1 933287386125820,
    decodeIntegerRow 32 3 1 1155243151184016,
    decodeIntegerRow 32 3 1 1612709264700208,
    decodeIntegerRow 32 3 1 1109496539856020,
    decodeIntegerRow 32 3 1 1475469430716220,
    decodeIntegerRow 32 3 1 923686233780496,
    decodeIntegerRow 32 3 1 918038512489648,
    decodeIntegerRow 32 3 1 924251007823060,
    decodeIntegerRow 32 3 1 919732834617340,
    decodeIntegerRow 32 3 1 697777037772816,
    decodeIntegerRow 32 3 1 240310924466608,
    decodeIntegerRow 32 3 1 743523649127060,
    decodeIntegerRow 32 3 1 377550758529340,
    decodeIntegerRow 32 3 1 697707301979820,
    decodeIntegerRow 32 3 1 240101717087620,
    decodeIntegerRow 32 3 1 1109552328406416,
    decodeIntegerRow 32 3 1 1475636796367408,
    decodeIntegerRow 32 3 1 923685364343020,
    decodeIntegerRow 32 3 1 918035904177220,
    decodeIntegerRow 32 3 1 928769880405136,
    decodeIntegerRow 32 3 1 933289452363568,
    decodeIntegerRow 32 3 1 697707302084780,
    decodeIntegerRow 32 3 1 240101717402500,
    decodeIntegerRow 32 3 1 1109552328275216,
    decodeIntegerRow 32 3 1 1475636795973808,
    decodeIntegerRow 32 3 1 923685372844780,
    decodeIntegerRow 32 3 1 918035929682500,
    decodeIntegerRow 32 3 1 928769869777936,
    decodeIntegerRow 32 3 1 933289420481968]

def innerRightBAC : Matrix (RightIndex 3 3 3) (RightIndex 3 3 3) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 3 3 3 r) []).getD (rightPosition 3 3 3 s) 0

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightBAC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightBAC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightBAC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightBAC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_2_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightBAC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_2_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightBAC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_3_0 : (innerRightZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightBAC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_3_1 : (innerRightZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightBAC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightBAC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightBAC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightBAC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightBAC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_2_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightBAC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_2_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightBAC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_3_0 : (innerRightZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightBAC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_3_1 : (innerRightZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightBAC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightBAC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightBAC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightBAC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightBAC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_2_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightBAC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_2_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightBAC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_3_0 : (innerRightZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightBAC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_3_1 : (innerRightZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightBAC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = innerRightBAC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = innerRightBAC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = innerRightBAC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = innerRightBAC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_2_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = innerRightBAC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_2_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = innerRightBAC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_3_0 : (innerRightZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = innerRightBAC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_3_1 : (innerRightZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = innerRightBAC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 3 3 3 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_1_0
  · exact innerRightBAC_row_0_1_1
  · exact innerRightBAC_row_0_2_0
  · exact innerRightBAC_row_0_2_1
  · exact innerRightBAC_row_0_3_0
  · exact innerRightBAC_row_0_3_1
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_1_0
  · exact innerRightBAC_row_1_1_1
  · exact innerRightBAC_row_1_2_0
  · exact innerRightBAC_row_1_2_1
  · exact innerRightBAC_row_1_3_0
  · exact innerRightBAC_row_1_3_1
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_1_0
  · exact innerRightBAC_row_2_1_1
  · exact innerRightBAC_row_2_2_0
  · exact innerRightBAC_row_2_2_1
  · exact innerRightBAC_row_2_3_0
  · exact innerRightBAC_row_2_3_1
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_1_0
  · exact innerRightBAC_row_3_1_1
  · exact innerRightBAC_row_3_2_0
  · exact innerRightBAC_row_3_2_1
  · exact innerRightBAC_row_3_3_0
  · exact innerRightBAC_row_3_3_1

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1146768960830324,
    decodeIntegerRow 32 3 1 1615533994468132,
    decodeIntegerRow 32 3 1 1116275897662428,
    decodeIntegerRow 32 3 1 1473209644343284,
    decodeIntegerRow 32 3 1 1477729206068236,
    decodeIntegerRow 32 3 1 750302975051868,
    decodeIntegerRow 32 3 1 243135645732772,
    decodeIntegerRow 32 3 1 1163717315927436,
    decodeIntegerRow 32 3 1 1102775068597836,
    decodeIntegerRow 32 3 1 1477895882970268,
    decodeIntegerRow 32 3 1 1163784468808292,
    decodeIntegerRow 32 3 1 1610094611118796,
    decodeIntegerRow 32 3 1 237277848252724,
    decodeIntegerRow 32 3 1 1146841279317732,
    decodeIntegerRow 32 3 1 1473377698740508,
    decodeIntegerRow 32 3 1 736690568876724,
    decodeIntegerRow 32 3 1 379642479087292,
    decodeIntegerRow 32 3 1 1116329588214996,
    decodeIntegerRow 32 3 1 237277856442196,
    decodeIntegerRow 32 3 1 1146841304935748,
    decodeIntegerRow 32 3 1 689235694635452,
    decodeIntegerRow 32 3 1 242925586552276,
    decodeIntegerRow 32 3 1 1102775036575316,
    decodeIntegerRow 32 3 1 1477895893207108,
    decodeIntegerRow 32 3 1 1609884534302332,
    decodeIntegerRow 32 3 1 689302847524116,
    decodeIntegerRow 32 3 1 1477729216301716,
    decodeIntegerRow 32 3 1 750303007064708,
    decodeIntegerRow 32 3 1 736744322939772,
    decodeIntegerRow 32 3 1 379810533487636,
    decodeIntegerRow 32 3 1 1146768986440596,
    decodeIntegerRow 32 3 1 1615533986281348]

def assocCAB : Matrix (RightIndex 3 3 3) (LeftIndex 3 3 3) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 3 3 3 r) []).getD (leftPosition 3 3 3 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocCAB ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocCAB ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_0 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocCAB ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_1_1 : (associatorZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocCAB ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_2_0 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocCAB ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_2_1 : (associatorZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocCAB ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_3_0 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocCAB ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_3_1 : (associatorZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocCAB ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocCAB ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocCAB ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_0 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocCAB ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_1_1 : (associatorZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocCAB ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_2_0 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocCAB ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_2_1 : (associatorZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocCAB ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_3_0 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocCAB ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_3_1 : (associatorZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocCAB ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_0 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocCAB ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_1 : (associatorZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocCAB ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_0 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocCAB ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_1_1 : (associatorZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocCAB ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_2_0 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocCAB ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_2_1 : (associatorZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocCAB ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_3_0 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocCAB ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_3_1 : (associatorZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocCAB ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_0 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = assocCAB ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_1 : (associatorZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = assocCAB ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_0 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = assocCAB ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_1_1 : (associatorZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = assocCAB ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_2_0 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = assocCAB ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_2_1 : (associatorZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = assocCAB ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_3_0 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = assocCAB ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_3_1 : (associatorZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = assocCAB ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 3 3 3 = assocCAB := by
  funext r
  fin_cases r
  · exact assocCAB_row_0_0_0
  · exact assocCAB_row_0_0_1
  · exact assocCAB_row_0_1_0
  · exact assocCAB_row_0_1_1
  · exact assocCAB_row_0_2_0
  · exact assocCAB_row_0_2_1
  · exact assocCAB_row_0_3_0
  · exact assocCAB_row_0_3_1
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_1_0
  · exact assocCAB_row_1_1_1
  · exact assocCAB_row_1_2_0
  · exact assocCAB_row_1_2_1
  · exact assocCAB_row_1_3_0
  · exact assocCAB_row_1_3_1
  · exact assocCAB_row_2_0_0
  · exact assocCAB_row_2_0_1
  · exact assocCAB_row_2_1_0
  · exact assocCAB_row_2_1_1
  · exact assocCAB_row_2_2_0
  · exact assocCAB_row_2_2_1
  · exact assocCAB_row_2_3_0
  · exact assocCAB_row_2_3_1
  · exact assocCAB_row_3_0_0
  · exact assocCAB_row_3_0_1
  · exact assocCAB_row_3_1_0
  · exact assocCAB_row_3_1_1
  · exact assocCAB_row_3_2_0
  · exact assocCAB_row_3_2_1
  · exact assocCAB_row_3_3_0
  · exact assocCAB_row_3_3_1

def outerLeftABC : Matrix (RightIndex 3 3 3) (LeftIndex 3 3 3) ℤ :=
  (show Matrix (Fin 4 × Fin 4 × Fin 2) (Fin 4 × Fin 4 × Fin 2) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 3 3) ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 3 3) ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_0 : (outerLeftZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_2_1 : (outerLeftZ 3 3 3) ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_0 : (outerLeftZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((0 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_3_1 : (outerLeftZ 3 3 3) ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((0 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 3 3) ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 3 3) ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_0 : (outerLeftZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_2_1 : (outerLeftZ 3 3 3) ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_0 : (outerLeftZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((1 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_3_1 : (outerLeftZ 3 3 3) ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((1 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 3 3) ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 3 3 3) ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_2_0 : (outerLeftZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_2_1 : (outerLeftZ 3 3 3) ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_3_0 : (outerLeftZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((2 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_3_1 : (outerLeftZ 3 3 3) ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((2 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (0 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 3 3) ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (0 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (1 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 3 3 3) ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (1 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_2_0 : (outerLeftZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (2 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_2_1 : (outerLeftZ 3 3 3) ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (2 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_3_0 : (outerLeftZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) = outerLeftABC ((3 : Fin 4), (3 : Fin 4), (0 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_3_1 : (outerLeftZ 3 3 3) ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) = outerLeftABC ((3 : Fin 4), (3 : Fin 4), (1 : Fin 2)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 3 3 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_2_0
  · exact outerLeftABC_row_0_2_1
  · exact outerLeftABC_row_0_3_0
  · exact outerLeftABC_row_0_3_1
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_2_0
  · exact outerLeftABC_row_1_2_1
  · exact outerLeftABC_row_1_3_0
  · exact outerLeftABC_row_1_3_1
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_2_0
  · exact outerLeftABC_row_2_2_1
  · exact outerLeftABC_row_2_3_0
  · exact outerLeftABC_row_2_3_1
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_2_0
  · exact outerLeftABC_row_3_2_1
  · exact outerLeftABC_row_3_3_0
  · exact outerLeftABC_row_3_3_1

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms333
