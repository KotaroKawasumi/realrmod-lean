import RMod.BrundanEllis.StackingReferenceHexagonAtoms335
import RMod.BrundanEllis.StackingReferenceHexagonAtoms353
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms533
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 3 3) (LeftIndex 5 3 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335.assocCAB

theorem assocABC_eq : associatorZ 5 3 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335.assocCAB_eq

def outerABC : Matrix (LeftIndex 3 3 5) (RightIndex 5 3 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 8) (Fin 4 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 5 3 3) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_4 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_5 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_6 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_7 : (outerRightZ 5 3 3) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 5 3 3) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_4 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_5 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_6 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_7 : (outerRightZ 5 3 3) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 5 3 3) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_4 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_5 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_6 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_7 : (outerRightZ 5 3 3) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 5 3 3) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_4 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_5 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_6 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_7 : (outerRightZ 5 3 3) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 3 3 = outerABC := by
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
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_0_4
  · exact outerABC_row_2_0_5
  · exact outerABC_row_2_0_6
  · exact outerABC_row_2_0_7
  · exact outerABC_row_2_1_0
  · exact outerABC_row_2_1_1
  · exact outerABC_row_2_1_2
  · exact outerABC_row_2_1_3
  · exact outerABC_row_2_1_4
  · exact outerABC_row_2_1_5
  · exact outerABC_row_2_1_6
  · exact outerABC_row_2_1_7
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_0_4
  · exact outerABC_row_3_0_5
  · exact outerABC_row_3_0_6
  · exact outerABC_row_3_0_7
  · exact outerABC_row_3_1_0
  · exact outerABC_row_3_1_1
  · exact outerABC_row_3_1_2
  · exact outerABC_row_3_1_3
  · exact outerABC_row_3_1_4
  · exact outerABC_row_3_1_5
  · exact outerABC_row_3_1_6
  · exact outerABC_row_3_1_7

def assocBAC : Matrix (RightIndex 3 5 3) (LeftIndex 3 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335.assocBCA

theorem assocBAC_eq : associatorZ 3 5 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335.assocBCA_eq

def innerABC : Matrix (LeftIndex 3 5 3) (LeftIndex 5 3 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_0 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_1 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_2 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_3 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_4 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_5 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_6 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_7 : (innerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_0 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_1 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_2 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_3 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_4 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_5 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_6 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_7 : (innerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_0 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_1 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_2 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_3 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_4 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_5 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_6 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_7 : (innerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_0 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_1 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_2 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_3 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_4 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_5 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_6 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_7 : (innerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 5 3 3 = innerABC := by
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
  · exact innerABC_row_4_0_0
  · exact innerABC_row_4_0_1
  · exact innerABC_row_4_0_2
  · exact innerABC_row_4_0_3
  · exact innerABC_row_4_0_4
  · exact innerABC_row_4_0_5
  · exact innerABC_row_4_0_6
  · exact innerABC_row_4_0_7
  · exact innerABC_row_5_0_0
  · exact innerABC_row_5_0_1
  · exact innerABC_row_5_0_2
  · exact innerABC_row_5_0_3
  · exact innerABC_row_5_0_4
  · exact innerABC_row_5_0_5
  · exact innerABC_row_5_0_6
  · exact innerABC_row_5_0_7
  · exact innerABC_row_6_0_0
  · exact innerABC_row_6_0_1
  · exact innerABC_row_6_0_2
  · exact innerABC_row_6_0_3
  · exact innerABC_row_6_0_4
  · exact innerABC_row_6_0_5
  · exact innerABC_row_6_0_6
  · exact innerABC_row_6_0_7
  · exact innerABC_row_7_0_0
  · exact innerABC_row_7_0_1
  · exact innerABC_row_7_0_2
  · exact innerABC_row_7_0_3
  · exact innerABC_row_7_0_4
  · exact innerABC_row_7_0_5
  · exact innerABC_row_7_0_6
  · exact innerABC_row_7_0_7

def innerRightABC : Matrix (RightIndex 5 3 3) (RightIndex 5 3 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms353.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 3 3 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms353.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 64 3 1 2897554982954507054731842505336,
    decodeIntegerRow 64 3 1 1222970223449979722641381551680,
    decodeIntegerRow 64 3 1 1449067880720130889938550628160,
    decodeIntegerRow 64 3 1 2822227385089355910184213181032,
    decodeIntegerRow 64 3 1 1193661775176433885492181119040,
    decodeIntegerRow 64 3 1 2910111233441095383976830271816,
    decodeIntegerRow 64 3 1 617732088666983396577370964008,
    decodeIntegerRow 64 3 1 1957399960069170525083945800640,
    decodeIntegerRow 64 3 1 617732140024461086764009046632,
    decodeIntegerRow 64 3 1 1957399947628083115165384520000,
    decodeIntegerRow 64 3 1 1193661798122280389280100963520,
    decodeIntegerRow 64 3 1 2910111178583811873083718763144,
    decodeIntegerRow 64 3 1 1984615950748985231280655225280,
    decodeIntegerRow 64 3 1 611456384137255865695711776808,
    decodeIntegerRow 64 3 1 536128781897345593374390823864,
    decodeIntegerRow 64 3 1 2210713621150079707418858070720,
    decodeIntegerRow 64 3 1 2910037848311567701821323448640,
    decodeIntegerRow 64 3 1 1193326756107685137995083510568,
    decodeIntegerRow 64 3 1 1475920125234549400854492316344,
    decodeIntegerRow 64 3 1 2815792198735876551736359807040,
    decodeIntegerRow 64 3 1 2211050530290305498826236685672,
    decodeIntegerRow 64 3 1 536210518174010803943277622720,
    decodeIntegerRow 64 3 1 2822076786048532555428114556480,
    decodeIntegerRow 64 3 1 1448707974537416627031130604424,
    decodeIntegerRow 64 3 1 611606983185490781536870640320,
    decodeIntegerRow 64 3 1 1984975856948596665902297598536,
    decodeIntegerRow 64 3 1 1222633265679092095085493699368,
    decodeIntegerRow 64 3 1 2897473357555750830400553915200,
    decodeIntegerRow 64 3 1 1475920137692360850921976801656,
    decodeIntegerRow 64 3 1 2815792147385396444198516989120,
    decodeIntegerRow 64 3 1 2910037793458078109821050758080,
    decodeIntegerRow 64 3 1 1193326779069183407694286503272,
    decodeIntegerRow 64 3 1 1984975845755094671508730994880,
    decodeIntegerRow 64 3 1 2822076786048532815459587889736,
    decodeIntegerRow 64 3 1 2897473302118501115674689884968,
    decodeIntegerRow 64 3 1 2211050530290306786665349657920,
    decodeIntegerRow 64 3 1 2815792198735876841138425928056,
    decodeIntegerRow 64 3 1 1957763695057961890902294440640,
    decodeIntegerRow 64 3 1 1193326756107683863717124667840,
    decodeIntegerRow 64 3 1 523645971980945316245306740072,
    decodeIntegerRow 64 3 1 2240357041223327802685543908800,
    decodeIntegerRow 64 3 1 2910037793458078643229858109912,
    decodeIntegerRow 64 3 1 617891672907116329861410302536,
    decodeIntegerRow 64 3 1 1475920137692359658020859360960,
    decodeIntegerRow 64 3 1 2897473357555751395440410714008,
    decodeIntegerRow 64 3 1 2211050554613419101733301622080,
    decodeIntegerRow 64 3 1 1984975856948597852020229664960,
    decodeIntegerRow 64 3 1 2822076837107021443089518561656,
    decodeIntegerRow 64 3 1 1957399960069171718147552547432,
    decodeIntegerRow 64 3 1 2815951731625528799066865605440,
    decodeIntegerRow 64 3 1 2910111233441095917021952680640,
    decodeIntegerRow 64 3 1 2240022045116077324799549444744,
    decodeIntegerRow 64 3 1 611456435203156834112523136960,
    decodeIntegerRow 64 3 1 1449067880720129703648376250408,
    decodeIntegerRow 64 3 1 2210713596842531474098148596664,
    decodeIntegerRow 64 3 1 2897554982954507619410131622080,
    decodeIntegerRow 64 3 1 2210713621150080995337117803144,
    decodeIntegerRow 64 3 1 2897555038395166326605193914560,
    decodeIntegerRow 64 3 1 611456384137255606056837976000,
    decodeIntegerRow 64 3 1 1449067869543528439667312810648,
    decodeIntegerRow 64 3 1 523572641708701144619278970560,
    decodeIntegerRow 64 3 1 1193661798122279114913922599864,
    decodeIntegerRow 64 3 1 1476283872664430562556126432472,
    decodeIntegerRow 64 3 1 617732140024460797750384463680]

def inverseACB : Matrix (LeftIndex 5 3 3) (RightIndex 5 3 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 3 3 r) []).getD (rightPosition 5 3 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_4 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_5 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_6 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_7 : (associatorInverseZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_4 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_5 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_6 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_7 : (associatorInverseZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_4 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_5 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_6 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_7 : (associatorInverseZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_4 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_5 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_6 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_7 : (associatorInverseZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 3 3 = inverseACB := by
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
  · exact inverseACB_row_4_0_0
  · exact inverseACB_row_4_0_1
  · exact inverseACB_row_4_0_2
  · exact inverseACB_row_4_0_3
  · exact inverseACB_row_4_0_4
  · exact inverseACB_row_4_0_5
  · exact inverseACB_row_4_0_6
  · exact inverseACB_row_4_0_7
  · exact inverseACB_row_5_0_0
  · exact inverseACB_row_5_0_1
  · exact inverseACB_row_5_0_2
  · exact inverseACB_row_5_0_3
  · exact inverseACB_row_5_0_4
  · exact inverseACB_row_5_0_5
  · exact inverseACB_row_5_0_6
  · exact inverseACB_row_5_0_7
  · exact inverseACB_row_6_0_0
  · exact inverseACB_row_6_0_1
  · exact inverseACB_row_6_0_2
  · exact inverseACB_row_6_0_3
  · exact inverseACB_row_6_0_4
  · exact inverseACB_row_6_0_5
  · exact inverseACB_row_6_0_6
  · exact inverseACB_row_6_0_7
  · exact inverseACB_row_7_0_0
  · exact inverseACB_row_7_0_1
  · exact inverseACB_row_7_0_2
  · exact inverseACB_row_7_0_3
  · exact inverseACB_row_7_0_4
  · exact inverseACB_row_7_0_5
  · exact inverseACB_row_7_0_6
  · exact inverseACB_row_7_0_7

def innerACB : Matrix (LeftIndex 3 5 3) (LeftIndex 5 3 3) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 5 3 3 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 3 3 5) (LeftIndex 3 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335.assocABC

theorem assocBCA_eq : associatorZ 3 3 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms335.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 3 5) (RightIndex 3 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms353.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 5 3 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms353.innerRightABC_eq

def assocCAB : Matrix (RightIndex 3 5 3) (LeftIndex 3 5 3) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 3 5 3 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 3 5 3) (LeftIndex 5 3 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 5 3 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 5 3 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 5 3 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 5 3 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_0 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_1 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_2 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_3 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_4 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_5 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_6 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_7 : (outerLeftZ 5 3 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_0 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_1 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_2 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_3 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_4 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_5 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_6 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_7 : (outerLeftZ 5 3 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_0 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_1 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_2 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_3 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_4 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_5 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_6 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_7 : (outerLeftZ 5 3 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_0 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_1 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_2 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_3 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_4 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_5 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_6 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_7 : (outerLeftZ 5 3 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 3 3 = outerLeftABC := by
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
  · exact outerLeftABC_row_4_0_0
  · exact outerLeftABC_row_4_0_1
  · exact outerLeftABC_row_4_0_2
  · exact outerLeftABC_row_4_0_3
  · exact outerLeftABC_row_4_0_4
  · exact outerLeftABC_row_4_0_5
  · exact outerLeftABC_row_4_0_6
  · exact outerLeftABC_row_4_0_7
  · exact outerLeftABC_row_5_0_0
  · exact outerLeftABC_row_5_0_1
  · exact outerLeftABC_row_5_0_2
  · exact outerLeftABC_row_5_0_3
  · exact outerLeftABC_row_5_0_4
  · exact outerLeftABC_row_5_0_5
  · exact outerLeftABC_row_5_0_6
  · exact outerLeftABC_row_5_0_7
  · exact outerLeftABC_row_6_0_0
  · exact outerLeftABC_row_6_0_1
  · exact outerLeftABC_row_6_0_2
  · exact outerLeftABC_row_6_0_3
  · exact outerLeftABC_row_6_0_4
  · exact outerLeftABC_row_6_0_5
  · exact outerLeftABC_row_6_0_6
  · exact outerLeftABC_row_6_0_7
  · exact outerLeftABC_row_7_0_0
  · exact outerLeftABC_row_7_0_1
  · exact outerLeftABC_row_7_0_2
  · exact outerLeftABC_row_7_0_3
  · exact outerLeftABC_row_7_0_4
  · exact outerLeftABC_row_7_0_5
  · exact outerLeftABC_row_7_0_6
  · exact outerLeftABC_row_7_0_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms533
