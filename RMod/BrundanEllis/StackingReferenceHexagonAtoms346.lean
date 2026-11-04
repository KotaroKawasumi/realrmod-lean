import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 644080544088088,
    decodeIntegerRow 32 3 1 333408061622236,
    decodeIntegerRow 32 3 1 1563671125708996,
    decodeIntegerRow 32 3 1 781906186706728,
    decodeIntegerRow 32 3 1 282570747890008,
    decodeIntegerRow 32 3 1 1056427696008796,
    decodeIntegerRow 32 3 1 659896625765956,
    decodeIntegerRow 32 3 1 330018919939048,
    decodeIntegerRow 32 3 1 926419179750168,
    decodeIntegerRow 32 3 1 926469458319196,
    decodeIntegerRow 32 3 1 926490292936516,
    decodeIntegerRow 32 3 1 926608240949288,
    decodeIntegerRow 32 3 1 926488054502488,
    decodeIntegerRow 32 3 1 926607207828956,
    decodeIntegerRow 32 3 1 926600492539076,
    decodeIntegerRow 32 3 1 926553141144808,
    decodeIntegerRow 32 3 1 1563671131745116,
    decodeIntegerRow 32 3 1 1071114032063272,
    decodeIntegerRow 32 3 1 644080571801752,
    decodeIntegerRow 32 3 1 1519612114842436,
    decodeIntegerRow 32 3 1 659896598209756,
    decodeIntegerRow 32 3 1 1523001282034792,
    decodeIntegerRow 32 3 1 282570754608472,
    decodeIntegerRow 32 3 1 796592522446276,
    decodeIntegerRow 32 3 1 926490292932004,
    decodeIntegerRow 32 3 1 926411947901528,
    decodeIntegerRow 32 3 1 926419179752168,
    decodeIntegerRow 32 3 1 926550730528444,
    decodeIntegerRow 32 3 1 926600492540964,
    decodeIntegerRow 32 3 1 926467047702808,
    decodeIntegerRow 32 3 1 926488054507048,
    decodeIntegerRow 32 3 1 926412981023804]

def assocABC : Matrix (RightIndex 3 4 6) (LeftIndex 3 4 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 4 6 r) []).getD (leftPosition 3 4 6 s) 0

private theorem assocABC_row_0_0_0 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_1 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_2 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_3 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_4 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_5 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_6 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_0_7 : (associatorZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_0 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_1 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_2 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_3 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_4 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_5 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_6 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_0_1_7 : (associatorZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_0 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_1 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_2 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_3 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_4 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_5 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_6 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_0_7 : (associatorZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_0 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_1 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_2 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_3 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_4 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_5 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_6 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocABC_row_1_1_7 : (associatorZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = assocABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocABC_eq : associatorZ 3 4 6 = assocABC := by
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
  · exact assocABC_row_0_1_0
  · exact assocABC_row_0_1_1
  · exact assocABC_row_0_1_2
  · exact assocABC_row_0_1_3
  · exact assocABC_row_0_1_4
  · exact assocABC_row_0_1_5
  · exact assocABC_row_0_1_6
  · exact assocABC_row_0_1_7
  · exact assocABC_row_1_0_0
  · exact assocABC_row_1_0_1
  · exact assocABC_row_1_0_2
  · exact assocABC_row_1_0_3
  · exact assocABC_row_1_0_4
  · exact assocABC_row_1_0_5
  · exact assocABC_row_1_0_6
  · exact assocABC_row_1_0_7
  · exact assocABC_row_1_1_0
  · exact assocABC_row_1_1_1
  · exact assocABC_row_1_1_2
  · exact assocABC_row_1_1_3
  · exact assocABC_row_1_1_4
  · exact assocABC_row_1_1_5
  · exact assocABC_row_1_1_6
  · exact assocABC_row_1_1_7

def outerABC : Matrix (LeftIndex 4 6 3) (RightIndex 3 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_4 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_5 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_6 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_7 : (outerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_4 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_5 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_6 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_7 : (outerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 4 6 = outerABC := by
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
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_0_1_4
  · exact outerABC_row_0_1_5
  · exact outerABC_row_0_1_6
  · exact outerABC_row_0_1_7
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_0_4
  · exact outerABC_row_1_0_5
  · exact outerABC_row_1_0_6
  · exact outerABC_row_1_0_7
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_1_1_4
  · exact outerABC_row_1_1_5
  · exact outerABC_row_1_1_6
  · exact outerABC_row_1_1_7

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 720367871280160,
    decodeIntegerRow 32 3 1 308083422153748,
    decodeIntegerRow 32 3 1 946841142057404,
    decodeIntegerRow 32 3 1 987503266061920,
    decodeIntegerRow 32 3 1 901088332003040,
    decodeIntegerRow 32 3 1 850244835811348,
    decodeIntegerRow 32 3 1 720869967171004,
    decodeIntegerRow 32 3 1 309589716203680,
    decodeIntegerRow 32 3 1 1132150220500000,
    decodeIntegerRow 32 3 1 1543430476190668,
    decodeIntegerRow 32 3 1 901088341554396,
    decodeIntegerRow 32 3 1 850244807157280,
    decodeIntegerRow 32 3 1 906179037213920,
    decodeIntegerRow 32 3 1 865516951531468,
    decodeIntegerRow 32 3 1 720367870335196,
    decodeIntegerRow 32 3 1 308083424988640,
    decodeIntegerRow 32 3 1 901094530729404,
    decodeIntegerRow 32 3 1 1002756756852640,
    decodeIntegerRow 32 3 1 1132087373468320,
    decodeIntegerRow 32 3 1 309778260842092,
    decodeIntegerRow 32 3 1 720305195254204,
    decodeIntegerRow 32 3 1 1545124794774880,
    decodeIntegerRow 32 3 1 906171298383200,
    decodeIntegerRow 32 3 1 987526511286892,
    decodeIntegerRow 32 3 1 906171288805596,
    decodeIntegerRow 32 3 1 987526482554080,
    decodeIntegerRow 32 3 1 1132714994542240,
    decodeIntegerRow 32 3 1 307895396910772,
    decodeIntegerRow 32 3 1 1132087372287196,
    decodeIntegerRow 32 3 1 309778257298720,
    decodeIntegerRow 32 3 1 951925648568160,
    decodeIntegerRow 32 3 1 850263403336372]

def assocBAC : Matrix (RightIndex 4 3 6) (LeftIndex 4 3 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 4 3 6 r) []).getD (leftPosition 4 3 6 s) 0

private theorem assocBAC_row_0_0_0 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_1 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_2 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_3 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_4 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_5 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_6 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_0_0_7 : (associatorZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_0 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_1 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_2 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_3 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_4 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_5 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_6 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_1_0_7 : (associatorZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_0 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_1 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_2 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_3 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_4 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_5 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_6 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_2_0_7 : (associatorZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_0 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_1 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_2 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_3 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_4 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_5 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_6 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBAC_row_3_0_7 : (associatorZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBAC_eq : associatorZ 4 3 6 = assocBAC := by
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

def innerABC : Matrix (LeftIndex 4 3 6) (LeftIndex 3 4 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 3 4 6 = innerABC := by
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
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_0_4
  · exact innerABC_row_1_0_5
  · exact innerABC_row_1_0_6
  · exact innerABC_row_1_0_7
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_0_4
  · exact innerABC_row_2_0_5
  · exact innerABC_row_2_0_6
  · exact innerABC_row_2_0_7
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_0_4
  · exact innerABC_row_3_0_5
  · exact innerABC_row_3_0_6
  · exact innerABC_row_3_0_7

def innerRightABC : Matrix (RightIndex 3 6 4) (RightIndex 3 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 3 4 6) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_4 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_5 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_6 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_7 : (innerRightZ 3 4 6) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 3 4 6) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_4 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_5 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_6 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_7 : (innerRightZ 3 4 6) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 4 6 = innerRightABC := by
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
  · exact innerRightABC_row_0_1_0
  · exact innerRightABC_row_0_1_1
  · exact innerRightABC_row_0_1_2
  · exact innerRightABC_row_0_1_3
  · exact innerRightABC_row_0_1_4
  · exact innerRightABC_row_0_1_5
  · exact innerRightABC_row_0_1_6
  · exact innerRightABC_row_0_1_7
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_1_0_4
  · exact innerRightABC_row_1_0_5
  · exact innerRightABC_row_1_0_6
  · exact innerRightABC_row_1_0_7
  · exact innerRightABC_row_1_1_0
  · exact innerRightABC_row_1_1_1
  · exact innerRightABC_row_1_1_2
  · exact innerRightABC_row_1_1_3
  · exact innerRightABC_row_1_1_4
  · exact innerRightABC_row_1_1_5
  · exact innerRightABC_row_1_1_6
  · exact innerRightABC_row_1_1_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 934229834558294,
    decodeIntegerRow 32 3 1 923999611251526,
    decodeIntegerRow 32 3 1 927346927465138,
    decodeIntegerRow 32 3 1 926224163756158,
    decodeIntegerRow 32 3 1 1544184652964854,
    decodeIntegerRow 32 3 1 720619349771686,
    decodeIntegerRow 32 3 1 995140342710418,
    decodeIntegerRow 32 3 1 903633258749278,
    decodeIntegerRow 32 3 1 926224192453918,
    decodeIntegerRow 32 3 1 925673270952658,
    decodeIntegerRow 32 3 1 923999608062874,
    decodeIntegerRow 32 3 1 918790353230666,
    decodeIntegerRow 32 3 1 903633259099198,
    decodeIntegerRow 32 3 1 857879846260978,
    decodeIntegerRow 32 3 1 720619349731834,
    decodeIntegerRow 32 3 1 308835535874026,
    decodeIntegerRow 32 3 1 308837860410082,
    decodeIntegerRow 32 3 1 720618574930222,
    decodeIntegerRow 32 3 1 995140600989286,
    decodeIntegerRow 32 3 1 949386844013494,
    decodeIntegerRow 32 3 1 918978640651202,
    decodeIntegerRow 32 3 1 923936849132302,
    decodeIntegerRow 32 3 1 927367848171526,
    decodeIntegerRow 32 3 1 926789051526934,
    decodeIntegerRow 32 3 1 949386843654826,
    decodeIntegerRow 32 3 1 857879587979194,
    decodeIntegerRow 32 3 1 720618574891342,
    decodeIntegerRow 32 3 1 1544182328455042,
    decodeIntegerRow 32 3 1 926789022829066,
    decodeIntegerRow 32 3 1 925652350246234,
    decodeIntegerRow 32 3 1 923936845943662,
    decodeIntegerRow 32 3 1 934041549263522]

def inverseACB : Matrix (LeftIndex 3 6 4) (RightIndex 3 6 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 6 4 r) []).getD (rightPosition 3 6 4 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 6 4 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 6 3 4) (LeftIndex 3 6 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 3 6 4) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 3 6 4) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_4 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_5 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_6 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_7 : (innerLeftZ 3 6 4) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_4 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_5 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_6 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_7 : (innerLeftZ 3 6 4) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 3 6 4 = innerACB := by
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

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 32 3 1 934229834558294,
    decodeIntegerRow 32 3 1 923999611251526,
    decodeIntegerRow 32 3 1 927346927465138,
    decodeIntegerRow 32 3 1 926224163756158,
    decodeIntegerRow 32 3 1 1544184652964854,
    decodeIntegerRow 32 3 1 720619349771686,
    decodeIntegerRow 32 3 1 995140342710418,
    decodeIntegerRow 32 3 1 903633258749278,
    decodeIntegerRow 32 3 1 926224192453918,
    decodeIntegerRow 32 3 1 925673270952658,
    decodeIntegerRow 32 3 1 923999608062874,
    decodeIntegerRow 32 3 1 918790353230666,
    decodeIntegerRow 32 3 1 903633259099198,
    decodeIntegerRow 32 3 1 857879846260978,
    decodeIntegerRow 32 3 1 720619349731834,
    decodeIntegerRow 32 3 1 308835535874026,
    decodeIntegerRow 32 3 1 308837860410082,
    decodeIntegerRow 32 3 1 720618574930222,
    decodeIntegerRow 32 3 1 995140600989286,
    decodeIntegerRow 32 3 1 949386844013494,
    decodeIntegerRow 32 3 1 918978640651202,
    decodeIntegerRow 32 3 1 923936849132302,
    decodeIntegerRow 32 3 1 927367848171526,
    decodeIntegerRow 32 3 1 926789051526934,
    decodeIntegerRow 32 3 1 949386843654826,
    decodeIntegerRow 32 3 1 857879587979194,
    decodeIntegerRow 32 3 1 720618574891342,
    decodeIntegerRow 32 3 1 1544182328455042,
    decodeIntegerRow 32 3 1 926789022829066,
    decodeIntegerRow 32 3 1 925652350246234,
    decodeIntegerRow 32 3 1 923936845943662,
    decodeIntegerRow 32 3 1 934041549263522]

def assocBCA : Matrix (RightIndex 4 6 3) (LeftIndex 4 6 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 4 6 3 r) []).getD (leftPosition 4 6 3 s) 0

private theorem assocBCA_row_0_0_0 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_1 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_2 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_3 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_4 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_5 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_6 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_0_0_7 : (associatorZ 4 6 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_0 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_1 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_2 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_3 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_4 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_5 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_6 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_1_0_7 : (associatorZ 4 6 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_0 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_1 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_2 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_3 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_4 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_5 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_6 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_2_0_7 : (associatorZ 4 6 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_0 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_1 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_2 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_3 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_4 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_5 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_6 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocBCA_row_3_0_7 : (associatorZ 4 6 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocBCA ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocBCA_eq : associatorZ 4 6 3 = assocBCA := by
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

def innerRightBAC : Matrix (RightIndex 4 6 3) (RightIndex 4 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 4 3 6 = innerRightBAC := by
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

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 32 3 1 857629831355212,
    decodeIntegerRow 32 3 1 948633352428136,
    decodeIntegerRow 32 3 1 1541638262277428,
    decodeIntegerRow 32 3 1 712982875736296,
    decodeIntegerRow 32 3 1 902880542373772,
    decodeIntegerRow 32 3 1 858131927246056,
    decodeIntegerRow 32 3 1 728254962714868,
    decodeIntegerRow 32 3 1 306291211783016,
    decodeIntegerRow 32 3 1 1140037341695416,
    decodeIntegerRow 32 3 1 1541638272197172,
    decodeIntegerRow 32 3 1 904386833220424,
    decodeIntegerRow 32 3 1 857629830336052,
    decodeIntegerRow 32 3 1 1546728967856696,
    decodeIntegerRow 32 3 1 728254991530612,
    decodeIntegerRow 32 3 1 994888260499144,
    decodeIntegerRow 32 3 1 902880545547892,
    decodeIntegerRow 32 3 1 1541644977565416,
    decodeIntegerRow 32 3 1 1140016306315852,
    decodeIntegerRow 32 3 1 857564744717416,
    decodeIntegerRow 32 3 1 904574347938868,
    decodeIntegerRow 32 3 1 728234128101736,
    decodeIntegerRow 32 3 1 1546721745219212,
    decodeIntegerRow 32 3 1 902691481173736,
    decodeIntegerRow 32 3 1 994827824005108,
    decodeIntegerRow 32 3 1 904574344738612,
    decodeIntegerRow 32 3 1 995455445162296,
    decodeIntegerRow 32 3 1 1140016334895412,
    decodeIntegerRow 32 3 1 311375201365704,
    decodeIntegerRow 32 3 1 994827822907252,
    decodeIntegerRow 32 3 1 950328704501176,
    decodeIntegerRow 32 3 1 1546721736008052,
    decodeIntegerRow 32 3 1 1124786031934024]

def assocCAB : Matrix (RightIndex 6 3 4) (LeftIndex 6 3 4) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 3 4 r) []).getD (leftPosition 6 3 4 s) 0

private theorem assocCAB_row_0_0_0 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_1 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_2 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_3 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_4 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_5 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_6 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_0_0_7 : (associatorZ 6 3 4) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_0 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_1 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_2 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_3 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_4 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_5 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_6 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_1_0_7 : (associatorZ 6 3 4) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_0 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_1 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_2 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_3 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_4 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_5 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_6 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_2_0_7 : (associatorZ 6 3 4) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_0 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_1 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_2 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_3 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_4 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_5 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_6 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem assocCAB_row_3_0_7 : (associatorZ 6 3 4) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = assocCAB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem assocCAB_eq : associatorZ 6 3 4 = assocCAB := by
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
  · exact assocCAB_row_1_0_0
  · exact assocCAB_row_1_0_1
  · exact assocCAB_row_1_0_2
  · exact assocCAB_row_1_0_3
  · exact assocCAB_row_1_0_4
  · exact assocCAB_row_1_0_5
  · exact assocCAB_row_1_0_6
  · exact assocCAB_row_1_0_7
  · exact assocCAB_row_2_0_0
  · exact assocCAB_row_2_0_1
  · exact assocCAB_row_2_0_2
  · exact assocCAB_row_2_0_3
  · exact assocCAB_row_2_0_4
  · exact assocCAB_row_2_0_5
  · exact assocCAB_row_2_0_6
  · exact assocCAB_row_2_0_7
  · exact assocCAB_row_3_0_0
  · exact assocCAB_row_3_0_1
  · exact assocCAB_row_3_0_2
  · exact assocCAB_row_3_0_3
  · exact assocCAB_row_3_0_4
  · exact assocCAB_row_3_0_5
  · exact assocCAB_row_3_0_6
  · exact assocCAB_row_3_0_7

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425408,
    decodeIntegerRow 32 3 1 926510094423664,
    decodeIntegerRow 32 3 1 926510094423820,
    decodeIntegerRow 32 3 1 926510094426920,
    decodeIntegerRow 32 3 1 926510094423808,
    decodeIntegerRow 32 3 1 926510094426864,
    decodeIntegerRow 32 3 1 926510094426380,
    decodeIntegerRow 32 3 1 926510094428200,
    decodeIntegerRow 32 3 1 926510091066688,
    decodeIntegerRow 32 3 1 926510079624304,
    decodeIntegerRow 32 3 1 926510080647820,
    decodeIntegerRow 32 3 1 926510100986920,
    decodeIntegerRow 32 3 1 926510080569088,
    decodeIntegerRow 32 3 1 926510100619504,
    decodeIntegerRow 32 3 1 926510097443980,
    decodeIntegerRow 32 3 1 926510109385000,
    decodeIntegerRow 32 3 1 926488054504768,
    decodeIntegerRow 32 3 1 926412981023344,
    decodeIntegerRow 32 3 1 926419696311820,
    decodeIntegerRow 32 3 1 926553141146920,
    decodeIntegerRow 32 3 1 926419179751168,
    decodeIntegerRow 32 3 1 926550730530544,
    decodeIntegerRow 32 3 1 926529895917580,
    decodeIntegerRow 32 3 1 926608240949800,
    decodeIntegerRow 32 3 1 781906171747648,
    decodeIntegerRow 32 3 1 289349060124784,
    decodeIntegerRow 32 3 1 333408067815820,
    decodeIntegerRow 32 3 1 1208939630906920,
    decodeIntegerRow 32 3 1 330018913378048,
    decodeIntegerRow 32 3 1 1193123576863984,
    decodeIntegerRow 32 3 1 1056427681207180,
    decodeIntegerRow 32 3 1 1570449437602600]

def outerLeftABC : Matrix (RightIndex 6 3 4) (LeftIndex 3 4 6) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 6 3 4 r) []).getD (leftPosition 3 4 6 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 3 4 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 3 4 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 3 4 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 3 4 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 4 6 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346
