import RMod.BrundanEllis.StackingReferenceHexagonAtoms337
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms373
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 3 7 3) (LeftIndex 3 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.assocBCA

theorem assocABC_eq : associatorZ 3 7 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.assocBCA_eq

def outerABC : Matrix (LeftIndex 7 3 3) (RightIndex 3 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_4 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_5 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_6 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_7 : (outerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_4 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_5 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_6 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_7 : (outerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 3 7 3 = outerABC := by
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

def assocBAC : Matrix (RightIndex 7 3 3) (LeftIndex 7 3 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.assocCAB

theorem assocBAC_eq : associatorZ 7 3 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 3 3) (LeftIndex 3 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.innerACB

theorem innerABC_eq : innerLeftZ 3 7 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 3 7) (RightIndex 3 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_4 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_5 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_6 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_7 : (innerRightZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_4 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_5 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_6 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_7 : (innerRightZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 3 7 3 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 928205880143908,
    decodeIntegerRow 32 3 1 918601824004960,
    decodeIntegerRow 32 3 1 919167456854560,
    decodeIntegerRow 32 3 1 923122052827708,
    decodeIntegerRow 32 3 1 1063868479158308,
    decodeIntegerRow 32 3 1 285938985164320,
    decodeIntegerRow 32 3 1 331755332180320,
    decodeIntegerRow 32 3 1 652079241282108,
    decodeIntegerRow 32 3 1 928203469522996,
    decodeIntegerRow 32 3 1 918602340564640,
    decodeIntegerRow 32 3 1 919166423735200,
    decodeIntegerRow 32 3 1 923119814394004,
    decodeIntegerRow 32 3 1 1063673219231796,
    decodeIntegerRow 32 3 1 285980826577120,
    decodeIntegerRow 32 3 1 331671649354720,
    decodeIntegerRow 32 3 1 651897928493204,
    decodeIntegerRow 32 3 1 1063868479079520,
    decodeIntegerRow 32 3 1 1567081204054948,
    decodeIntegerRow 32 3 1 1521264857012668,
    decodeIntegerRow 32 3 1 652079241439520,
    decodeIntegerRow 32 3 1 928205873762080,
    decodeIntegerRow 32 3 1 934418394608548,
    decodeIntegerRow 32 3 1 933852759630268,
    decodeIntegerRow 32 3 1 923122065578080,
    decodeIntegerRow 32 3 1 1063673219153120,
    decodeIntegerRow 32 3 1 1567039362642124,
    decodeIntegerRow 32 3 1 1521348539838316,
    decodeIntegerRow 32 3 1 651897928650720,
    decodeIntegerRow 32 3 1 928203463150240,
    decodeIntegerRow 32 3 1 934417878046924,
    decodeIntegerRow 32 3 1 933853792753516,
    decodeIntegerRow 32 3 1 923119827152800]

def inverseACB : Matrix (LeftIndex 3 3 7) (RightIndex 3 3 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 3 7 r) []).getD (rightPosition 3 3 7 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 3 3 7) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 3 3 7) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_4 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_5 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_6 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_7 : (associatorInverseZ 3 3 7) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_4 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_5 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_6 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_7 : (associatorInverseZ 3 3 7) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = inverseACB ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 3 3 7 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 3 3 7) (LeftIndex 3 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.innerABC

theorem innerACB_eq : innerLeftZ 3 3 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.innerABC_eq

def assocBCA : Matrix (RightIndex 7 3 3) (LeftIndex 7 3 3) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 7 3 3 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 32 3 1 720932729408176,
    decodeIntegerRow 32 3 1 309778002207472,
    decodeIntegerRow 32 3 1 951924883294580,
    decodeIntegerRow 32 3 1 1002754432290340,
    decodeIntegerRow 32 3 1 946841926465776,
    decodeIntegerRow 32 3 1 987505561882672,
    decodeIntegerRow 32 3 1 1132652232541300,
    decodeIntegerRow 32 3 1 1544936505228580,
    decodeIntegerRow 32 3 1 1132087458498736,
    decodeIntegerRow 32 3 1 1543242189479152,
    decodeIntegerRow 32 3 1 901095315137780,
    decodeIntegerRow 32 3 1 850265727819940,
    decodeIntegerRow 32 3 1 906178271940336,
    decodeIntegerRow 32 3 1 865514598306352,
    decodeIntegerRow 32 3 1 720367957491700,
    decodeIntegerRow 32 3 1 308083680079780,
    decodeIntegerRow 32 3 1 951932631702900,
    decodeIntegerRow 32 3 1 850242511327780,
    decodeIntegerRow 32 3 1 720870053382544,
    decodeIntegerRow 32 3 1 1543430214722128,
    decodeIntegerRow 32 3 1 1132715080753780,
    decodeIntegerRow 32 3 1 307895138984740,
    decodeIntegerRow 32 3 1 946848125192144,
    decodeIntegerRow 32 3 1 865496030781328,
    decodeIntegerRow 32 3 1 951932622125300,
    decodeIntegerRow 32 3 1 850242482594980,
    decodeIntegerRow 32 3 1 720870054327184,
    decodeIntegerRow 32 3 1 1543430217556048,
    decodeIntegerRow 32 3 1 1132715079572980,
    decodeIntegerRow 32 3 1 307895135442340,
    decodeIntegerRow 32 3 1 946848115640784,
    decodeIntegerRow 32 3 1 865496002127248]

def innerRightBAC : Matrix (RightIndex 7 3 3) (RightIndex 7 3 3) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 7 3 3 r) []).getD (rightPosition 7 3 3 s) 0

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_4 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_5 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_6 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_7 : (innerRightZ 7 3 3) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_4 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_5 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_6 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_7 : (innerRightZ 7 3 3) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_4 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_5 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_6 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_7 : (innerRightZ 7 3 3) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_4 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_5 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_6 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_7 : (innerRightZ 7 3 3) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = innerRightBAC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 7 3 3 = innerRightBAC := by
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

def assocCAB : Matrix (RightIndex 3 3 7) (LeftIndex 3 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.assocABC

theorem assocCAB_eq : associatorZ 3 3 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms337.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 3 7) (LeftIndex 3 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 3 7 3) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_4 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_5 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_6 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_7 : (outerLeftZ 3 7 3) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 3 7 3) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_4 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_5 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_6 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_7 : (outerLeftZ 3 7 3) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerLeftABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 3 7 3 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms373
