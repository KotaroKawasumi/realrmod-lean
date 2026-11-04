import RMod.BrundanEllis.StackingReferenceHexagonAtoms355
import RMod.BrundanEllis.StackingReferenceHexagonAtoms535
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms553
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 5 3) (LeftIndex 5 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBCA

theorem assocABC_eq : associatorZ 5 5 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBCA_eq

def outerABC : Matrix (LeftIndex 5 3 5) (RightIndex 5 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_0 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_1 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_2 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_3 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_4 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_5 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_6 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_7 : (outerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_0 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_1 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_2 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_3 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_4 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_5 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_6 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_7 : (outerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_0 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_1 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_2 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_3 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_4 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_5 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_6 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_7 : (outerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_0 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_1 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_2 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_3 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_4 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_5 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_6 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_7 : (outerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 5 3 = outerABC := by
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
  · exact outerABC_row_4_0_0
  · exact outerABC_row_4_0_1
  · exact outerABC_row_4_0_2
  · exact outerABC_row_4_0_3
  · exact outerABC_row_4_0_4
  · exact outerABC_row_4_0_5
  · exact outerABC_row_4_0_6
  · exact outerABC_row_4_0_7
  · exact outerABC_row_5_0_0
  · exact outerABC_row_5_0_1
  · exact outerABC_row_5_0_2
  · exact outerABC_row_5_0_3
  · exact outerABC_row_5_0_4
  · exact outerABC_row_5_0_5
  · exact outerABC_row_5_0_6
  · exact outerABC_row_5_0_7
  · exact outerABC_row_6_0_0
  · exact outerABC_row_6_0_1
  · exact outerABC_row_6_0_2
  · exact outerABC_row_6_0_3
  · exact outerABC_row_6_0_4
  · exact outerABC_row_6_0_5
  · exact outerABC_row_6_0_6
  · exact outerABC_row_6_0_7
  · exact outerABC_row_7_0_0
  · exact outerABC_row_7_0_1
  · exact outerABC_row_7_0_2
  · exact outerABC_row_7_0_3
  · exact outerABC_row_7_0_4
  · exact outerABC_row_7_0_5
  · exact outerABC_row_7_0_6
  · exact outerABC_row_7_0_7

def assocBAC : Matrix (RightIndex 5 5 3) (LeftIndex 5 5 3) ℤ := assocABC

theorem assocBAC_eq : associatorZ 5 5 3 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 5 5 3) (LeftIndex 5 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms535.innerACB

theorem innerABC_eq : innerLeftZ 5 5 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms535.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 3 5) (RightIndex 5 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 5 5 3) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 5 5 3) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_4 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_5 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_6 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_7 : (innerRightZ 5 5 3) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_4 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_5 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_6 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_7 : (innerRightZ 5 5 3) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_0 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_1 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_2 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_3 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_4 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_5 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_6 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_7 : (innerRightZ 5 5 3) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_0 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_1 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_2 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_3 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_4 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_5 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_6 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_7 : (innerRightZ 5 5 3) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_0 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_1 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_2 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_3 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_4 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_5 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_6 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_7 : (innerRightZ 5 5 3) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_0 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_1 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_2 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_3 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_4 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_5 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_6 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_7 : (innerRightZ 5 5 3) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 5 5 3 = innerRightABC := by
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
  · exact innerRightABC_row_4_0_0
  · exact innerRightABC_row_4_0_1
  · exact innerRightABC_row_4_0_2
  · exact innerRightABC_row_4_0_3
  · exact innerRightABC_row_4_0_4
  · exact innerRightABC_row_4_0_5
  · exact innerRightABC_row_4_0_6
  · exact innerRightABC_row_4_0_7
  · exact innerRightABC_row_5_0_0
  · exact innerRightABC_row_5_0_1
  · exact innerRightABC_row_5_0_2
  · exact innerRightABC_row_5_0_3
  · exact innerRightABC_row_5_0_4
  · exact innerRightABC_row_5_0_5
  · exact innerRightABC_row_5_0_6
  · exact innerRightABC_row_5_0_7
  · exact innerRightABC_row_6_0_0
  · exact innerRightABC_row_6_0_1
  · exact innerRightABC_row_6_0_2
  · exact innerRightABC_row_6_0_3
  · exact innerRightABC_row_6_0_4
  · exact innerRightABC_row_6_0_5
  · exact innerRightABC_row_6_0_6
  · exact innerRightABC_row_6_0_7
  · exact innerRightABC_row_7_0_0
  · exact innerRightABC_row_7_0_1
  · exact innerRightABC_row_7_0_2
  · exact innerRightABC_row_7_0_3
  · exact innerRightABC_row_7_0_4
  · exact innerRightABC_row_7_0_5
  · exact innerRightABC_row_7_0_6
  · exact innerRightABC_row_7_0_7

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1716320713254230103363218355520,
    decodeIntegerRow 64 3 1 1715271150338009926484915651872,
    decodeIntegerRow 64 3 1 1712132047337003500059288475240,
    decodeIntegerRow 64 3 1 1702711435424686029935267094400,
    decodeIntegerRow 64 3 1 1674625201045592908397226473920,
    decodeIntegerRow 64 3 1 1589610285595812311701442397472,
    decodeIntegerRow 64 3 1 1335340869243233822764429108840,
    decodeIntegerRow 64 3 1 572274175524105178479189626240,
    decodeIntegerRow 64 3 1 1730972367141049652689787745280,
    decodeIntegerRow 64 3 1 1712131994159674956163767021376,
    decodeIntegerRow 64 3 1 1718412671932149473413377451600,
    decodeIntegerRow 64 3 1 1716320719160153811335737390720,
    decodeIntegerRow 64 3 1 2861409644549558621597686529280,
    decodeIntegerRow 64 3 1 1335340868586722358675913658176,
    decodeIntegerRow 64 3 1 1844073534721115612906589816400,
    decodeIntegerRow 64 3 1 1674625201118505409590176103040,
    decodeIntegerRow 64 3 1 1843957235222794201680808781440,
    decodeIntegerRow 64 3 1 1674276302623541176414930056880,
    decodeIntegerRow 64 3 1 572287097687894338164656058176,
    decodeIntegerRow 64 3 1 2098381717540611551239628320000,
    decodeIntegerRow 64 3 1 1718411234166632285338649733760,
    decodeIntegerRow 64 3 1 1716316405863602247117761468080,
    decodeIntegerRow 64 3 1 1702711594958472746408308461376,
    decodeIntegerRow 64 3 1 1721552251553867271814211200000,
    decodeIntegerRow 64 3 1 2098381718197127956715314042240,
    decodeIntegerRow 64 3 1 2861396722385790874589957940840,
    decodeIntegerRow 64 3 1 1674276302696520660856187811808,
    decodeIntegerRow 64 3 1 1589726585045503060714423001920,
    decodeIntegerRow 64 3 1 1721552304731796163748530710400,
    decodeIntegerRow 64 3 1 1730972207609064061672847054440,
    decodeIntegerRow 64 3 1 1716316411774929365350126909408,
    decodeIntegerRow 64 3 1 1715272584164443505820549392320,
    decodeIntegerRow 64 3 1 1715272584164443505258011655104,
    decodeIntegerRow 64 3 1 1716316411774929363654775916800,
    decodeIntegerRow 64 3 1 1702711612683448417901557356160,
    decodeIntegerRow 64 3 1 1712131515560716305658027749040,
    decodeIntegerRow 64 3 1 1589726585045503015149124410304,
    decodeIntegerRow 64 3 1 1674276302696520523532670976000,
    decodeIntegerRow 64 3 1 572287097906721198306548019840,
    decodeIntegerRow 64 3 1 1335302102095383292588768792240,
    decodeIntegerRow 64 3 1 1712131568738645228094909386272,
    decodeIntegerRow 64 3 1 1730972225334039733166038553920,
    decodeIntegerRow 64 3 1 1716316405863602248813114595200,
    decodeIntegerRow 64 3 1 1718411234166632284776118370920,
    decodeIntegerRow 64 3 1 1335302102751902168771986787872,
    decodeIntegerRow 64 3 1 2861396722604617734731849193920,
    decodeIntegerRow 64 3 1 1674276302623541313738446919040,
    decodeIntegerRow 64 3 1 1843957235222794156115510268520,
    decodeIntegerRow 64 3 1 1674625201118505546788168700520,
    decodeIntegerRow 64 3 1 1844073534721115566964718509440,
    decodeIntegerRow 64 3 1 2098342951705788890642116313920,
    decodeIntegerRow 64 3 1 572274175742954274863347101408,
    decodeIntegerRow 64 3 1 1716320719160153813029538710120,
    decodeIntegerRow 64 3 1 1718412671932149472846190665600,
    decodeIntegerRow 64 3 1 1721551826132837513242963625920,
    decodeIntegerRow 64 3 1 1702711453151462837052022583008,
    decodeIntegerRow 64 3 1 2861409644768407717981844713040,
    decodeIntegerRow 64 3 1 2098342951049279897233238861440,
    decodeIntegerRow 64 3 1 1589610285595812265759571169280,
    decodeIntegerRow 64 3 1 1674625201045592771199233850304,
    decodeIntegerRow 64 3 1 1730972384867826459806600629840,
    decodeIntegerRow 64 3 1 1721551772955508999849659925120,
    decodeIntegerRow 64 3 1 1715271150338009925917735246080,
    decodeIntegerRow 64 3 1 1716320713254230101669414919104]

def inverseACB : Matrix (LeftIndex 5 3 5) (RightIndex 5 3 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 3 5 r) []).getD (rightPosition 5 3 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_4 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_5 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_6 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_7 : (associatorInverseZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_4 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_5 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_6 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_7 : (associatorInverseZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_4 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_5 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_6 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_7 : (associatorInverseZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_4 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_5 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_6 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_7 : (associatorInverseZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 3 5 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 3 5 5) (LeftIndex 5 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms535.innerABC

theorem innerACB_eq : innerLeftZ 5 3 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms535.innerABC_eq

def assocBCA : Matrix (RightIndex 5 3 5) (LeftIndex 5 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBAC

theorem assocBCA_eq : associatorZ 5 3 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 5 3 5) (RightIndex 5 5 3) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 5 3 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 3 5 5) (LeftIndex 3 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocABC

theorem assocCAB_eq : associatorZ 3 5 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 5 5) (LeftIndex 5 5 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 8) (Fin 4 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_4 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_5 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_6 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_7 : (outerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_4 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_5 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_6 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_7 : (outerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_4 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_5 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_6 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_7 : (outerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_4 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_5 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_6 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_7 : (outerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 5 3 = outerLeftABC := by
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
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_0_4
  · exact outerLeftABC_row_2_0_5
  · exact outerLeftABC_row_2_0_6
  · exact outerLeftABC_row_2_0_7
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_1_2
  · exact outerLeftABC_row_2_1_3
  · exact outerLeftABC_row_2_1_4
  · exact outerLeftABC_row_2_1_5
  · exact outerLeftABC_row_2_1_6
  · exact outerLeftABC_row_2_1_7
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_0_4
  · exact outerLeftABC_row_3_0_5
  · exact outerLeftABC_row_3_0_6
  · exact outerLeftABC_row_3_0_7
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_1_2
  · exact outerLeftABC_row_3_1_3
  · exact outerLeftABC_row_3_1_4
  · exact outerLeftABC_row_3_1_5
  · exact outerLeftABC_row_3_1_6
  · exact outerLeftABC_row_3_1_7

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms553
