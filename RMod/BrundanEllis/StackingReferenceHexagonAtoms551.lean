import RMod.BrundanEllis.StackingReferenceHexagonAtoms515
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms551
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 5 1) (LeftIndex 5 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.assocCAB

theorem assocABC_eq : associatorZ 5 5 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.assocCAB_eq

def outerABC : Matrix (LeftIndex 5 1 5) (RightIndex 5 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_4 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_5 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_6 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_7 : (outerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_4 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_5 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_6 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_7 : (outerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_4 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_5 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_6 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_7 : (outerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_4 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_5 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_6 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_7 : (outerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = outerABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 5 1 = outerABC := by
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

def assocBAC : Matrix (RightIndex 5 5 1) (LeftIndex 5 5 1) ℤ := assocABC

theorem assocBAC_eq : associatorZ 5 5 1 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 5 5 1) (LeftIndex 5 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.innerACB

theorem innerABC_eq : innerLeftZ 5 5 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 1 5) (RightIndex 5 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 8) (Fin 2 × Fin 2 × Fin 8) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_4 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_5 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_6 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_7 : (innerRightZ 5 5 1) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_0 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_1 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_2 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_3 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_4 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_5 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_6 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_1_7 : (innerRightZ 5 5 1) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_4 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_5 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_6 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_7 : (innerRightZ 5 5 1) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_0 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_1 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_2 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_3 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_4 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_5 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_6 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_1_7 : (innerRightZ 5 5 1) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = innerRightABC ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 5 5 1 = innerRightABC := by
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

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 311408781167476,
    decodeIntegerRow 32 3 1 1124869384243040,
    decodeIntegerRow 32 3 1 857600917739680,
    decodeIntegerRow 32 3 1 950244683493892,
    decodeIntegerRow 32 3 1 1139932292894240,
    decodeIntegerRow 32 3 1 306262287404884,
    decodeIntegerRow 32 3 1 904491002924572,
    decodeIntegerRow 32 3 1 994861385491360,
    decodeIntegerRow 32 3 1 1140121355116388,
    decodeIntegerRow 32 3 1 1546692811629280,
    decodeIntegerRow 32 3 1 948550010620000,
    decodeIntegerRow 32 3 1 994854699018796,
    decodeIntegerRow 32 3 1 1541671842078880,
    decodeIntegerRow 32 3 1 1124681873828612,
    decodeIntegerRow 32 3 1 857593657310836,
    decodeIntegerRow 32 3 1 902796521369440,
    decodeIntegerRow 32 3 1 995426502962692,
    decodeIntegerRow 32 3 1 950223676698400,
    decodeIntegerRow 32 3 1 311348343571360,
    decodeIntegerRow 32 3 1 728338316125964,
    decodeIntegerRow 32 3 1 948550020535840,
    decodeIntegerRow 32 3 1 994854670201372,
    decodeIntegerRow 32 3 1 1140121354093356,
    decodeIntegerRow 32 3 1 1546692814804960,
    decodeIntegerRow 32 3 1 904491012849196,
    decodeIntegerRow 32 3 1 994861414305760,
    decodeIntegerRow 32 3 1 1139932293918240,
    decodeIntegerRow 32 3 1 306262290580252,
    decodeIntegerRow 32 3 1 995419299693280,
    decodeIntegerRow 32 3 1 902775514565236,
    decodeIntegerRow 32 3 1 1541611404482428,
    decodeIntegerRow 32 3 1 728150803507040]

def inverseACB : Matrix (LeftIndex 5 1 5) (RightIndex 5 1 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 1 5 r) []).getD (rightPosition 5 1 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_4 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_5 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_6 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_7 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_4 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_5 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_6 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_7 : (associatorInverseZ 5 1 5) ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((0 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_4 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_5 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_6 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_7 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (0 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_4 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_5 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_6 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_7 : (associatorInverseZ 5 1 5) ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) = inverseACB ((1 : Fin 2), (1 : Fin 2), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 1 5 = inverseACB := by
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

def innerACB : Matrix (LeftIndex 1 5 5) (LeftIndex 5 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.innerABC

theorem innerACB_eq : innerLeftZ 5 1 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.innerABC_eq

def assocBCA : Matrix (RightIndex 5 1 5) (LeftIndex 5 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.assocABC

theorem assocBCA_eq : associatorZ 5 1 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 1 5) (RightIndex 5 5 1) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 5 1 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 5 5) (LeftIndex 1 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.assocBAC

theorem assocCAB_eq : associatorZ 1 5 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms515.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425408,
    decodeIntegerRow 32 3 1 926510094423808,
    decodeIntegerRow 32 3 1 926510094423664,
    decodeIntegerRow 32 3 1 926510094424976,
    decodeIntegerRow 32 3 1 926510094423820,
    decodeIntegerRow 32 3 1 926510094425460,
    decodeIntegerRow 32 3 1 926510094426920,
    decodeIntegerRow 32 3 1 926510094428200,
    decodeIntegerRow 32 3 1 926510091066688,
    decodeIntegerRow 32 3 1 926510080569088,
    decodeIntegerRow 32 3 1 926510079624304,
    decodeIntegerRow 32 3 1 926510088232336,
    decodeIntegerRow 32 3 1 926510080647820,
    decodeIntegerRow 32 3 1 926510091407860,
    decodeIntegerRow 32 3 1 926510100986920,
    decodeIntegerRow 32 3 1 926510109385000,
    decodeIntegerRow 32 3 1 926488054504768,
    decodeIntegerRow 32 3 1 926419179751168,
    decodeIntegerRow 32 3 1 926412981023344,
    decodeIntegerRow 32 3 1 926469458321296,
    decodeIntegerRow 32 3 1 926419696311820,
    decodeIntegerRow 32 3 1 926490292934260,
    decodeIntegerRow 32 3 1 926553141146920,
    decodeIntegerRow 32 3 1 926608240949800,
    decodeIntegerRow 32 3 1 781906171747648,
    decodeIntegerRow 32 3 1 330018913378048,
    decodeIntegerRow 32 3 1 289349060124784,
    decodeIntegerRow 32 3 1 659896611987856,
    decodeIntegerRow 32 3 1 333408067815820,
    decodeIntegerRow 32 3 1 796592507644660,
    decodeIntegerRow 32 3 1 1208939630906920,
    decodeIntegerRow 32 3 1 1570449437602600]

def outerLeftABC : Matrix (RightIndex 1 5 5) (LeftIndex 5 5 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 5 5 r) []).getD (leftPosition 5 5 1 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_4 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_5 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_6 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_7 : (outerLeftZ 5 5 1) ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((0 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_4 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_5 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_6 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_7 : (outerLeftZ 5 5 1) ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((1 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_4 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_5 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_6 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_7 : (outerLeftZ 5 5 1) ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((2 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (0 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (1 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (2 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (3 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_4 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (4 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_5 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (5 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_6 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (6 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_7 : (outerLeftZ 5 5 1) ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) = outerLeftABC ((3 : Fin 4), (0 : Fin 1), (7 : Fin 8)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 5 1 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms551
