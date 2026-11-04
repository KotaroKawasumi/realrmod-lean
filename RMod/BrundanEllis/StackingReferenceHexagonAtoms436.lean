import RMod.BrundanEllis.StackingReferenceHexagonAtoms346
import RMod.BrundanEllis.StackingReferenceHexagonAtoms364
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms436
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 3 6) (LeftIndex 4 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocBAC

theorem assocABC_eq : associatorZ 4 3 6 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocBAC_eq

def outerABC : Matrix (LeftIndex 3 6 4) (RightIndex 4 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_4 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_5 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_6 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_7 : (outerRightZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_4 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_5 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_6 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_7 : (outerRightZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 4 3 6 = outerABC := by
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

def assocBAC : Matrix (RightIndex 3 4 6) (LeftIndex 3 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocABC

theorem assocBAC_eq : associatorZ 3 4 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.assocABC_eq

def innerABC : Matrix (LeftIndex 3 4 6) (LeftIndex 4 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 8) (Fin 4 × Fin 1 × Fin 8) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_4 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_5 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_6 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_7 : (innerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_4 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_5 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_6 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_7 : (innerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_4 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_5 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_6 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_7 : (innerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_4 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_5 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_6 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_7 : (innerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 4 3 6 = innerABC := by
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

def innerRightABC : Matrix (RightIndex 4 6 3) (RightIndex 4 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.innerRightBAC

theorem innerRightABC_eq : innerRightZ 4 3 6 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 1544186977671416,
    decodeIntegerRow 32 3 1 1132390766108320,
    decodeIntegerRow 32 3 1 857848336021120,
    decodeIntegerRow 32 3 1 903727445143252,
    decodeIntegerRow 32 3 1 934135749306616,
    decodeIntegerRow 32 3 1 929051826331360,
    decodeIntegerRow 32 3 1 925662419991040,
    decodeIntegerRow 32 3 1 926228826621652,
    decodeIntegerRow 32 3 1 934135720608640,
    decodeIntegerRow 32 3 1 923968352955028,
    decodeIntegerRow 32 3 1 927357772050904,
    decodeIntegerRow 32 3 1 926228827680160,
    decodeIntegerRow 32 3 1 1544186977317120,
    decodeIntegerRow 32 3 1 720629422625428,
    decodeIntegerRow 32 3 1 995171852870104,
    decodeIntegerRow 32 3 1 903727445156320,
    decodeIntegerRow 32 3 1 926226502094344,
    decodeIntegerRow 32 3 1 925663194830560,
    decodeIntegerRow 32 3 1 923968104240640,
    decodeIntegerRow 32 3 1 918884525638828,
    decodeIntegerRow 32 3 1 903539158785544,
    decodeIntegerRow 32 3 1 857911098140320,
    decodeIntegerRow 32 3 1 720608502037120,
    decodeIntegerRow 32 3 1 308840184749228,
    decodeIntegerRow 32 3 1 949481030053120,
    decodeIntegerRow 32 3 1 857911098100972,
    decodeIntegerRow 32 3 1 720608501919016,
    decodeIntegerRow 32 3 1 1544180003748320,
    decodeIntegerRow 32 3 1 926793685690240,
    decodeIntegerRow 32 3 1 925663191643372,
    decodeIntegerRow 32 3 1 923968094674216,
    decodeIntegerRow 32 3 1 934135634515360]

def inverseACB : Matrix (LeftIndex 4 6 3) (RightIndex 4 6 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 6 3 r) []).getD (rightPosition 4 6 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_4 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_5 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_6 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_7 : (associatorInverseZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_4 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_5 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_6 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_7 : (associatorInverseZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 4 6 3 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 6 4 3) (LeftIndex 4 6 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_4 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_5 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_6 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_7 : (innerLeftZ 4 6 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_2 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_3 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_4 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_5 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_6 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_7 : (innerLeftZ 4 6 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_4 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_5 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_6 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_7 : (innerLeftZ 4 6 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_2 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_3 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_4 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_5 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_6 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_7 : (innerLeftZ 4 6 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 4 6 3 = innerACB := by
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

def assocBCA : Matrix (RightIndex 3 6 4) (LeftIndex 3 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.assocABC

theorem assocBCA_eq : associatorZ 3 6 4 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 6 4) (RightIndex 3 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 4 6 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms346.innerRightABC_eq

def assocCAB : Matrix (RightIndex 6 4 3) (LeftIndex 6 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.assocBCA

theorem assocCAB_eq : associatorZ 6 4 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms364.assocBCA_eq

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

def outerLeftABC : Matrix (RightIndex 6 4 3) (LeftIndex 4 3 6) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 6 4 3 r) []).getD (leftPosition 4 3 6 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 4 3 6) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 4 3 6) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 4 3 6) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 4 3 6) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 4 3 6 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms436
