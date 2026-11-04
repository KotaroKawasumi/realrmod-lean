import RMod.BrundanEllis.StackingReferenceHexagonAtoms355
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms535
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 3 5) (LeftIndex 5 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBAC

theorem assocABC_eq : associatorZ 5 3 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBAC_eq

def outerABC : Matrix (LeftIndex 3 5 5) (RightIndex 5 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_0 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_1 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_2 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_3 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_4 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_5 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_6 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_7 : (outerRightZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_0 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_1 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_2 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_3 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_4 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_5 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_6 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_7 : (outerRightZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_0 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_1 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_2 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_3 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_4 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_5 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_6 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_7 : (outerRightZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_0 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_1 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_2 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_3 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_4 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_5 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_6 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_7 : (outerRightZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 3 5 = outerABC := by
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

def assocBAC : Matrix (RightIndex 3 5 5) (LeftIndex 3 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocABC

theorem assocBAC_eq : associatorZ 3 5 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocABC_eq

def innerABC : Matrix (LeftIndex 3 5 5) (LeftIndex 5 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_0 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_1 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_2 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_3 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_4 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_5 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_6 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_4_0_7 : (innerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_0 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_1 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_2 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_3 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_4 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_5 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_6 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_5_0_7 : (innerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_0 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_1 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_2 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_3 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_4 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_5 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_6 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_6_0_7 : (innerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_0 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_1 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_2 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_3 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_4 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_5 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_6 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_7_0_7 : (innerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = innerABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 5 3 5 = innerABC := by
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

def innerRightABC : Matrix (RightIndex 5 5 3) (RightIndex 5 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 3 5 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1713700867223698638605163923152,
    decodeIntegerRow 64 3 1 1731497717458175286833227848640,
    decodeIntegerRow 64 3 1 1730446714828410917824978896640,
    decodeIntegerRow 64 3 1 1723121602998022866691694739496,
    decodeIntegerRow 64 3 1 1462417433419112575252261369552,
    decodeIntegerRow 64 3 1 2903962302411747026267174941760,
    decodeIntegerRow 64 3 1 2818831089400733088192909665280,
    decodeIntegerRow 64 3 1 2225497031139363928751486662696,
    decodeIntegerRow 64 3 1 1971111332725309295449231422400,
    decodeIntegerRow 64 3 1 2903626381300677761540270464112,
    decodeIntegerRow 64 3 1 2819192961194616695447672042664,
    decodeIntegerRow 64 3 1 1208109232535976183421138693120,
    decodeIntegerRow 64 3 1 1719981038820071986579277423680,
    decodeIntegerRow 64 3 1 1731493570283964555365190528112,
    decodeIntegerRow 64 3 1 1730451182381421826737774570664,
    decodeIntegerRow 64 3 1 1710561259805388724562346146560,
    decodeIntegerRow 64 3 1 2903626381300677776224195403520,
    decodeIntegerRow 64 3 1 1971111332725309288671439264984,
    decodeIntegerRow 64 3 1 1208109232535976180030951212752,
    decodeIntegerRow 64 3 1 2819192961194616679629379937600,
    decodeIntegerRow 64 3 1 1731493570283965744763110620160,
    decodeIntegerRow 64 3 1 1719981038820071437578112672984,
    decodeIntegerRow 64 3 1 1710561259805388449957160236752,
    decodeIntegerRow 64 3 1 1730451182381420545456114060480,
    decodeIntegerRow 64 3 1 1731497717458176476621723063464,
    decodeIntegerRow 64 3 1 1713700867223699187690037008640,
    decodeIntegerRow 64 3 1 1723121602998023141129527752640,
    decodeIntegerRow 64 3 1 1730446714828409636905884442768,
    decodeIntegerRow 64 3 1 2903962302411747040955921796264,
    decodeIntegerRow 64 3 1 1462417433419112582031086963200,
    decodeIntegerRow 64 3 1 2225497031139363932139608057920,
    decodeIntegerRow 64 3 1 2818831089400733072379093684368,
    decodeIntegerRow 64 3 1 2225497054775666716781720320048,
    decodeIntegerRow 64 3 1 2818831140617225301317325358400,
    decodeIntegerRow 64 3 1 529721462741399857143888719360,
    decodeIntegerRow 64 3 1 1971266398687048464361794377944,
    decodeIntegerRow 64 3 1 1723121603289829073951333632048,
    decodeIntegerRow 64 3 1 1730446715460713290826485132480,
    decodeIntegerRow 64 3 1 1702186102153604289167225893120,
    decodeIntegerRow 64 3 1 1719982953214661359076823113944,
    decodeIntegerRow 64 3 1 1723122560195362025320396498240,
    decodeIntegerRow 64 3 1 1703232638543185492660429356688,
    decodeIntegerRow 64 3 1 1731493569603038932608154580056,
    decodeIntegerRow 64 3 1 1719981038674135528586074589440,
    decodeIntegerRow 64 3 1 2225574564123835784453604717760,
    decodeIntegerRow 64 3 1 614490910297577403181328838288,
    decodeIntegerRow 64 3 1 2903626326145702318222597127256,
    decodeIntegerRow 64 3 1 1971111320904456197998768806400,
    decodeIntegerRow 64 3 1 1703232638543186773942149379840,
    decodeIntegerRow 64 3 1 1723122560195362299925595158744,
    decodeIntegerRow 64 3 1 1719981038674134979584884327632,
    decodeIntegerRow 64 3 1 1731493569603040122006129951040,
    decodeIntegerRow 64 3 1 614490910297577418999621678080,
    decodeIntegerRow 64 3 1 2225574564123835787843792355544,
    decodeIntegerRow 64 3 1 1971111320904456191220976334032,
    decodeIntegerRow 64 3 1 2903626326145702332906522749120,
    decodeIntegerRow 64 3 1 2818831140617225285503510112424,
    decodeIntegerRow 64 3 1 2225497054775666720169841557760,
    decodeIntegerRow 64 3 1 1971266398687048457582969099200,
    decodeIntegerRow 64 3 1 529721462741399842455142547088,
    decodeIntegerRow 64 3 1 1730446715460712009907450208424,
    decodeIntegerRow 64 3 1 1723121603289829348389153886720,
    decodeIntegerRow 64 3 1 1719982953214660809991975535680,
    decodeIntegerRow 64 3 1 1702186102153603099378785939088]

def inverseACB : Matrix (LeftIndex 5 5 3) (RightIndex 5 5 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 5 3 r) []).getD (rightPosition 5 5 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_4 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_5 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_6 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_7 : (associatorInverseZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_4 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_5 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_6 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_7 : (associatorInverseZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_2 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_3 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_4 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_5 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_6 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_7 : (associatorInverseZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_2 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_3 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_4 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_5 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_6 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_7 : (associatorInverseZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 5 3 = inverseACB := by
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
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_0_4
  · exact inverseACB_row_2_0_5
  · exact inverseACB_row_2_0_6
  · exact inverseACB_row_2_0_7
  · exact inverseACB_row_2_1_0
  · exact inverseACB_row_2_1_1
  · exact inverseACB_row_2_1_2
  · exact inverseACB_row_2_1_3
  · exact inverseACB_row_2_1_4
  · exact inverseACB_row_2_1_5
  · exact inverseACB_row_2_1_6
  · exact inverseACB_row_2_1_7
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_0_4
  · exact inverseACB_row_3_0_5
  · exact inverseACB_row_3_0_6
  · exact inverseACB_row_3_0_7
  · exact inverseACB_row_3_1_0
  · exact inverseACB_row_3_1_1
  · exact inverseACB_row_3_1_2
  · exact inverseACB_row_3_1_3
  · exact inverseACB_row_3_1_4
  · exact inverseACB_row_3_1_5
  · exact inverseACB_row_3_1_6
  · exact inverseACB_row_3_1_7

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 64 3 1 1716844143606710847805623514792,
    decodeIntegerRow 64 3 1 1716841431547576139648217851716,
    decodeIntegerRow 64 3 1 1716842867343561406127734872484,
    decodeIntegerRow 64 3 1 1716843984073724493709641492952,
    decodeIntegerRow 64 3 1 1717022820443057053088171101672,
    decodeIntegerRow 64 3 1 1716803143653119754008735093956,
    decodeIntegerRow 64 3 1 1716919443128026386688702885924,
    decodeIntegerRow 64 3 1 1717009898271173487740957947672,
    decodeIntegerRow 64 3 1 1731495644187121639348224429352,
    decodeIntegerRow 64 3 1 1713701824202200093687616726596,
    decodeIntegerRow 64 3 1 1723122081669638575923515148964,
    decodeIntegerRow 64 3 1 1730448948264552983463802543192,
    decodeIntegerRow 64 3 1 2903794367456353397503577289832,
    decodeIntegerRow 64 3 1 1462494948677708195040942365636,
    decodeIntegerRow 64 3 1 2225535803540225271397585037604,
    decodeIntegerRow 64 3 1 2819011997728292272559723567512,
    decodeIntegerRow 64 3 1 1716843984073724219188144788004,
    decodeIntegerRow 64 3 1 1716840952948949797429764373912,
    decodeIntegerRow 64 3 1 1716841431547574950054980433048,
    decodeIntegerRow 64 3 1 1716839676685802185895250870844,
    decodeIntegerRow 64 3 1 1717009898271173484351803667364,
    decodeIntegerRow 64 3 1 1716764377164486082153092501592,
    decodeIntegerRow 64 3 1 1716803143653119739322398829528,
    decodeIntegerRow 64 3 1 1716660999849455438347986941884,
    decodeIntegerRow 64 3 1 1730448948264552983421961132324,
    decodeIntegerRow 64 3 1 1710561738622873908539074018072,
    decodeIntegerRow 64 3 1 1713701824202200093506303933208,
    decodeIntegerRow 64 3 1 1702188176105390845393307486524,
    decodeIntegerRow 64 3 1 2819011997728292272559207006884,
    decodeIntegerRow 64 3 1 1208148016752287213257853435352,
    decodeIntegerRow 64 3 1 1462494948677708195038703936088,
    decodeIntegerRow 64 3 1 529889452836159087155304920764,
    decodeIntegerRow 64 3 1 1971188847980302637210237134556,
    decodeIntegerRow 64 3 1 2903794316248266483955793180008,
    decodeIntegerRow 64 3 1 2819012052875462794841952608872,
    decodeIntegerRow 64 3 1 1208148004935036387056929257156,
    decodeIntegerRow 64 3 1 1719981995798528419952866075996,
    decodeIntegerRow 64 3 1 1731495643554923035477264130728,
    decodeIntegerRow 64 3 1 1730448948945382249170990557992,
    decodeIntegerRow 64 3 1 1710561738476981923225650798916,
    decodeIntegerRow 64 3 1 1716880676635790459401986383836,
    decodeIntegerRow 64 3 1 1717022820435252132052727068648,
    decodeIntegerRow 64 3 1 1717009898279578787317590055912,
    decodeIntegerRow 64 3 1 1716764377162684962345582555076,
    decodeIntegerRow 64 3 1 1716842388744891872525128554076,
    decodeIntegerRow 64 3 1 1716844143606614490755796841768,
    decodeIntegerRow 64 3 1 1716843984073828262840229950632,
    decodeIntegerRow 64 3 1 1716840952948928842287875629636,
    decodeIntegerRow 64 3 1 2225535815357476097603330448552,
    decodeIntegerRow 64 3 1 2819012052875462794841436048196,
    decodeIntegerRow 64 3 1 529889504044246000703089030564,
    decodeIntegerRow 64 3 1 1971188847980302637212475563992,
    decodeIntegerRow 64 3 1 1723122081815530561627458221032,
    decodeIntegerRow 64 3 1 1730448948945382249129149143236,
    decodeIntegerRow 64 3 1 1702188176737589449264267783204,
    decodeIntegerRow 64 3 1 1719981995798528420134178860312,
    decodeIntegerRow 64 3 1 1716919443129827538128320918312,
    decodeIntegerRow 64 3 1 1717009898279578783928435460676,
    decodeIntegerRow 64 3 1 1716660999857260359383430817444,
    decodeIntegerRow 64 3 1 1716880676635790474088321913432,
    decodeIntegerRow 64 3 1 1716842867343584923470378572392,
    decodeIntegerRow 64 3 1 1716843984073827988318707736516,
    decodeIntegerRow 64 3 1 1716839676685898542945064789284,
    decodeIntegerRow 64 3 1 1716842388744893062118306451352]

def innerACB : Matrix (LeftIndex 5 5 3) (LeftIndex 5 5 3) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 5 5 3 r) []).getD (leftPosition 5 5 3 s) 0

private theorem innerACB_row_0_0_0 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 5 5 3) ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_2 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_3 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_4 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_5 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_6 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_7 : (innerLeftZ 5 5 3) ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 5 5 3) ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_2 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_3 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_4 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_5 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_6 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_7 : (innerLeftZ 5 5 3) ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_0 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_1 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_2 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_3 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_4 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_5 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_6 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_0_7 : (innerLeftZ 5 5 3) ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerACB ((2 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_0 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_1 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_2 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_3 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_4 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_5 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_6 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_2_1_7 : (innerLeftZ 5 5 3) ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerACB ((2 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_0 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_1 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_2 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_3 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_4 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_5 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_6 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_0_7 : (innerLeftZ 5 5 3) ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) = innerACB ((3 : Fin 4), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_0 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_1 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_2 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_3 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_4 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_5 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_6 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_3_1_7 : (innerLeftZ 5 5 3) ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) = innerACB ((3 : Fin 4), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 5 5 3 = innerACB := by
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
  · exact innerACB_row_0_1_0
  · exact innerACB_row_0_1_1
  · exact innerACB_row_0_1_2
  · exact innerACB_row_0_1_3
  · exact innerACB_row_0_1_4
  · exact innerACB_row_0_1_5
  · exact innerACB_row_0_1_6
  · exact innerACB_row_0_1_7
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_0_4
  · exact innerACB_row_1_0_5
  · exact innerACB_row_1_0_6
  · exact innerACB_row_1_0_7
  · exact innerACB_row_1_1_0
  · exact innerACB_row_1_1_1
  · exact innerACB_row_1_1_2
  · exact innerACB_row_1_1_3
  · exact innerACB_row_1_1_4
  · exact innerACB_row_1_1_5
  · exact innerACB_row_1_1_6
  · exact innerACB_row_1_1_7
  · exact innerACB_row_2_0_0
  · exact innerACB_row_2_0_1
  · exact innerACB_row_2_0_2
  · exact innerACB_row_2_0_3
  · exact innerACB_row_2_0_4
  · exact innerACB_row_2_0_5
  · exact innerACB_row_2_0_6
  · exact innerACB_row_2_0_7
  · exact innerACB_row_2_1_0
  · exact innerACB_row_2_1_1
  · exact innerACB_row_2_1_2
  · exact innerACB_row_2_1_3
  · exact innerACB_row_2_1_4
  · exact innerACB_row_2_1_5
  · exact innerACB_row_2_1_6
  · exact innerACB_row_2_1_7
  · exact innerACB_row_3_0_0
  · exact innerACB_row_3_0_1
  · exact innerACB_row_3_0_2
  · exact innerACB_row_3_0_3
  · exact innerACB_row_3_0_4
  · exact innerACB_row_3_0_5
  · exact innerACB_row_3_0_6
  · exact innerACB_row_3_0_7
  · exact innerACB_row_3_1_0
  · exact innerACB_row_3_1_1
  · exact innerACB_row_3_1_2
  · exact innerACB_row_3_1_3
  · exact innerACB_row_3_1_4
  · exact innerACB_row_3_1_5
  · exact innerACB_row_3_1_6
  · exact innerACB_row_3_1_7

def assocBCA : Matrix (RightIndex 3 5 5) (LeftIndex 3 5 5) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 3 5 5 = assocBCA := assocBAC_eq

def innerRightBAC : Matrix (RightIndex 3 5 5) (RightIndex 3 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 5 5 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 5 3) (LeftIndex 5 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBCA

theorem assocCAB_eq : associatorZ 5 5 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms355.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 5 5 3) (LeftIndex 5 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 8) (Fin 8 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 5 3 5) ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 5 3 5) ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 5 3 5) ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 5 3 5) ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_0 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_1 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_2 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_3 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_4 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_5 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_6 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_4_0_7 : (outerLeftZ 5 3 5) ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((4 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_0 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_1 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_2 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_3 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_4 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_5 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_6 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_5_0_7 : (outerLeftZ 5 3 5) ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((5 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_0 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_1 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_2 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_3 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_4 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_5 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_6 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_6_0_7 : (outerLeftZ 5 3 5) ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((6 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_0 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_1 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_2 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_3 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_4 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_5 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_6 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_7_0_7 : (outerLeftZ 5 3 5) ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((7 : Fin 8), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 3 5 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms535
