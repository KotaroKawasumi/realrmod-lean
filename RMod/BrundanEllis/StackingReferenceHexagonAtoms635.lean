import RMod.BrundanEllis.StackingReferenceHexagonAtoms356
import RMod.BrundanEllis.StackingReferenceHexagonAtoms365
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms635
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 3 5) (LeftIndex 6 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocCAB

theorem assocABC_eq : associatorZ 6 3 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocCAB_eq

def outerABC : Matrix (LeftIndex 3 5 6) (RightIndex 6 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 6 3 5) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 6 3 5) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 6 3 5) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 6 3 5) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_0 : (outerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_1 : (outerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_2 : (outerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_3 : (outerRightZ 6 3 5) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_0 : (outerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_1 : (outerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_2 : (outerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_3 : (outerRightZ 6 3 5) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_0 : (outerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_1 : (outerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_2 : (outerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_3 : (outerRightZ 6 3 5) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_0 : (outerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_1 : (outerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_2 : (outerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_3 : (outerRightZ 6 3 5) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 6 3 5 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_4_0_0
  · exact outerABC_row_4_0_1
  · exact outerABC_row_4_0_2
  · exact outerABC_row_4_0_3
  · exact outerABC_row_5_0_0
  · exact outerABC_row_5_0_1
  · exact outerABC_row_5_0_2
  · exact outerABC_row_5_0_3
  · exact outerABC_row_6_0_0
  · exact outerABC_row_6_0_1
  · exact outerABC_row_6_0_2
  · exact outerABC_row_6_0_3
  · exact outerABC_row_7_0_0
  · exact outerABC_row_7_0_1
  · exact outerABC_row_7_0_2
  · exact outerABC_row_7_0_3

def assocBAC : Matrix (RightIndex 3 6 5) (LeftIndex 3 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocABC

theorem assocBAC_eq : associatorZ 3 6 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.assocABC_eq

def innerABC : Matrix (LeftIndex 3 6 5) (LeftIndex 6 3 5) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerABC_row_0_0_0 : (innerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_1 : (innerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_2 : (innerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_0_3 : (innerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_0 : (innerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_1 : (innerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_2 : (innerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_0_1_3 : (innerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_0 : (innerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_1 : (innerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_2 : (innerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_0_3 : (innerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_0 : (innerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_1 : (innerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_2 : (innerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_1_1_3 : (innerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_0 : (innerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_1 : (innerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_2 : (innerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_0_3 : (innerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_0 : (innerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_1 : (innerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_2 : (innerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_2_1_3 : (innerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_0 : (innerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_1 : (innerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_2 : (innerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_0_3 : (innerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_0 : (innerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_1 : (innerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_2 : (innerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerABC_row_3_1_3 : (innerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerABC_eq : innerLeftZ 6 3 5 = innerABC := by
  funext r
  fin_cases r
  · exact innerABC_row_0_0_0
  · exact innerABC_row_0_0_1
  · exact innerABC_row_0_0_2
  · exact innerABC_row_0_0_3
  · exact innerABC_row_0_1_0
  · exact innerABC_row_0_1_1
  · exact innerABC_row_0_1_2
  · exact innerABC_row_0_1_3
  · exact innerABC_row_1_0_0
  · exact innerABC_row_1_0_1
  · exact innerABC_row_1_0_2
  · exact innerABC_row_1_0_3
  · exact innerABC_row_1_1_0
  · exact innerABC_row_1_1_1
  · exact innerABC_row_1_1_2
  · exact innerABC_row_1_1_3
  · exact innerABC_row_2_0_0
  · exact innerABC_row_2_0_1
  · exact innerABC_row_2_0_2
  · exact innerABC_row_2_0_3
  · exact innerABC_row_2_1_0
  · exact innerABC_row_2_1_1
  · exact innerABC_row_2_1_2
  · exact innerABC_row_2_1_3
  · exact innerABC_row_3_0_0
  · exact innerABC_row_3_0_1
  · exact innerABC_row_3_0_2
  · exact innerABC_row_3_0_3
  · exact innerABC_row_3_1_0
  · exact innerABC_row_3_1_1
  · exact innerABC_row_3_1_2
  · exact innerABC_row_3_1_3

def innerRightABC : Matrix (RightIndex 6 5 3) (RightIndex 6 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 3 5 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 957017128647724,
    decodeIntegerRow 32 3 1 992608693252844,
    decodeIntegerRow 32 3 1 1133280024975436,
    decodeIntegerRow 32 3 1 1543995162959116,
    decodeIntegerRow 32 3 1 957007840082560,
    decodeIntegerRow 32 3 1 992588518676480,
    decodeIntegerRow 32 3 1 1133217005284480,
    decodeIntegerRow 32 3 1 1543806959388160,
    decodeIntegerRow 32 3 1 1131522685283200,
    decodeIntegerRow 32 3 1 308648453296000,
    decodeIntegerRow 32 3 1 941758960071040,
    decodeIntegerRow 32 3 1 855348684666240,
    decodeIntegerRow 32 3 1 1131585190539268,
    decodeIntegerRow 32 3 1 308460083915452,
    decodeIntegerRow 32 3 1 941763618722212,
    decodeIntegerRow 32 3 1 855327017803548,
    decodeIntegerRow 32 3 1 1133217004576000,
    decodeIntegerRow 32 3 1 309213226157440,
    decodeIntegerRow 32 3 1 957007830557440,
    decodeIntegerRow 32 3 1 860431641468800,
    decodeIntegerRow 32 3 1 719740163167708,
    decodeIntegerRow 32 3 1 1543995159651868,
    decodeIntegerRow 32 3 1 896003050676092,
    decodeIntegerRow 32 3 1 992608664537532,
    decodeIntegerRow 32 3 1 941763609115444,
    decodeIntegerRow 32 3 1 997693199737356,
    decodeIntegerRow 32 3 1 1131585189121876,
    decodeIntegerRow 32 3 1 1544560108007404,
    decodeIntegerRow 32 3 1 911261219176960,
    decodeIntegerRow 32 3 1 855348713346560,
    decodeIntegerRow 32 3 1 721497502151680,
    decodeIntegerRow 32 3 1 308648456366080]

def inverseACB : Matrix (LeftIndex 6 5 3) (RightIndex 6 5 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 5 3 r) []).getD (rightPosition 6 5 3 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_0 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_1 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_2 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_2_3 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_0 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_1 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_2 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_3_3 : (associatorInverseZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = inverseACB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_0 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_1 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_2 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_2_3 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_0 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_1 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_2 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_3_3 : (associatorInverseZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = inverseACB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 6 5 3 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_0_1_0
  · exact inverseACB_row_0_1_1
  · exact inverseACB_row_0_1_2
  · exact inverseACB_row_0_1_3
  · exact inverseACB_row_0_2_0
  · exact inverseACB_row_0_2_1
  · exact inverseACB_row_0_2_2
  · exact inverseACB_row_0_2_3
  · exact inverseACB_row_0_3_0
  · exact inverseACB_row_0_3_1
  · exact inverseACB_row_0_3_2
  · exact inverseACB_row_0_3_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_1_2_0
  · exact inverseACB_row_1_2_1
  · exact inverseACB_row_1_2_2
  · exact inverseACB_row_1_2_3
  · exact inverseACB_row_1_3_0
  · exact inverseACB_row_1_3_1
  · exact inverseACB_row_1_3_2
  · exact inverseACB_row_1_3_3

def innerACB : Matrix (LeftIndex 5 6 3) (LeftIndex 6 5 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 4) (Fin 2 × Fin 4 × Fin 4) ℤ from 1)

private theorem innerACB_row_0_0_0 : (innerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerACB ((0 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_1 : (innerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerACB ((0 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_2 : (innerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerACB ((0 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_0_3 : (innerLeftZ 6 5 3) ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerACB ((0 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_0 : (innerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerACB ((0 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_1 : (innerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerACB ((0 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_2 : (innerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerACB ((0 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_1_3 : (innerLeftZ 6 5 3) ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerACB ((0 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_2_0 : (innerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerACB ((0 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_2_1 : (innerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerACB ((0 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_2_2 : (innerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerACB ((0 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_2_3 : (innerLeftZ 6 5 3) ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerACB ((0 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_3_0 : (innerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerACB ((0 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_3_1 : (innerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerACB ((0 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_3_2 : (innerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerACB ((0 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_0_3_3 : (innerLeftZ 6 5 3) ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerACB ((0 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_0 : (innerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) = innerACB ((1 : Fin 2), (0 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_1 : (innerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) = innerACB ((1 : Fin 2), (0 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_2 : (innerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) = innerACB ((1 : Fin 2), (0 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_0_3 : (innerLeftZ 6 5 3) ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) = innerACB ((1 : Fin 2), (0 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_0 : (innerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) = innerACB ((1 : Fin 2), (1 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_1 : (innerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) = innerACB ((1 : Fin 2), (1 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_2 : (innerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) = innerACB ((1 : Fin 2), (1 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_1_3 : (innerLeftZ 6 5 3) ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) = innerACB ((1 : Fin 2), (1 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_2_0 : (innerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) = innerACB ((1 : Fin 2), (2 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_2_1 : (innerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) = innerACB ((1 : Fin 2), (2 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_2_2 : (innerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) = innerACB ((1 : Fin 2), (2 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_2_3 : (innerLeftZ 6 5 3) ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) = innerACB ((1 : Fin 2), (2 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_3_0 : (innerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) = innerACB ((1 : Fin 2), (3 : Fin 4), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_3_1 : (innerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) = innerACB ((1 : Fin 2), (3 : Fin 4), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_3_2 : (innerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) = innerACB ((1 : Fin 2), (3 : Fin 4), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerACB_row_1_3_3 : (innerLeftZ 6 5 3) ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) = innerACB ((1 : Fin 2), (3 : Fin 4), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerACB_eq : innerLeftZ 6 5 3 = innerACB := by
  funext r
  fin_cases r
  · exact innerACB_row_0_0_0
  · exact innerACB_row_0_0_1
  · exact innerACB_row_0_0_2
  · exact innerACB_row_0_0_3
  · exact innerACB_row_0_1_0
  · exact innerACB_row_0_1_1
  · exact innerACB_row_0_1_2
  · exact innerACB_row_0_1_3
  · exact innerACB_row_0_2_0
  · exact innerACB_row_0_2_1
  · exact innerACB_row_0_2_2
  · exact innerACB_row_0_2_3
  · exact innerACB_row_0_3_0
  · exact innerACB_row_0_3_1
  · exact innerACB_row_0_3_2
  · exact innerACB_row_0_3_3
  · exact innerACB_row_1_0_0
  · exact innerACB_row_1_0_1
  · exact innerACB_row_1_0_2
  · exact innerACB_row_1_0_3
  · exact innerACB_row_1_1_0
  · exact innerACB_row_1_1_1
  · exact innerACB_row_1_1_2
  · exact innerACB_row_1_1_3
  · exact innerACB_row_1_2_0
  · exact innerACB_row_1_2_1
  · exact innerACB_row_1_2_2
  · exact innerACB_row_1_2_3
  · exact innerACB_row_1_3_0
  · exact innerACB_row_1_3_1
  · exact innerACB_row_1_3_2
  · exact innerACB_row_1_3_3

def assocBCA : Matrix (RightIndex 3 5 6) (LeftIndex 3 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocABC

theorem assocBCA_eq : associatorZ 3 5 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 5 6) (RightIndex 3 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 6 5 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms365.innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 6 3) (LeftIndex 5 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBCA

theorem assocCAB_eq : associatorZ 5 6 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms356.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425919,
    decodeIntegerRow 32 3 1 926510094425917,
    decodeIntegerRow 32 3 1 926510094425911,
    decodeIntegerRow 32 3 1 926510094425893,
    decodeIntegerRow 32 3 1 926510094425839,
    decodeIntegerRow 32 3 1 926510094425677,
    decodeIntegerRow 32 3 1 926510094425191,
    decodeIntegerRow 32 3 1 926510094423733,
    decodeIntegerRow 32 3 1 926510094419359,
    decodeIntegerRow 32 3 1 926510094406237,
    decodeIntegerRow 32 3 1 926510094366871,
    decodeIntegerRow 32 3 1 926510094248773,
    decodeIntegerRow 32 3 1 926510093894479,
    decodeIntegerRow 32 3 1 926510092831597,
    decodeIntegerRow 32 3 1 926510089642951,
    decodeIntegerRow 32 3 1 926510080077013,
    decodeIntegerRow 32 3 1 926510137472641,
    decodeIntegerRow 32 3 1 926510223566083,
    decodeIntegerRow 32 3 1 926510481846409,
    decodeIntegerRow 32 3 1 926511256687387,
    decodeIntegerRow 32 3 1 926513581210321,
    decodeIntegerRow 32 3 1 926520554779123,
    decodeIntegerRow 32 3 1 926541475485529,
    decodeIntegerRow 32 3 1 926604237604747,
    decodeIntegerRow 32 3 1 926792523962401,
    decodeIntegerRow 32 3 1 927357383035363,
    decodeIntegerRow 32 3 1 929051960254249,
    decodeIntegerRow 32 3 1 934135691910907,
    decodeIntegerRow 32 3 1 949386886880881,
    decodeIntegerRow 32 3 1 995140471790803,
    decodeIntegerRow 32 3 1 1132401226520569,
    decodeIntegerRow 32 3 1 1544183490709867]

def outerLeftABC : Matrix (RightIndex 5 6 3) (LeftIndex 6 3 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 6 3 r) []).getD (leftPosition 6 3 5 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 6 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 6 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 6 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 6 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 6 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 6 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 6 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 6 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 6 3 5 = outerLeftABC := by
  funext r
  fin_cases r
  · exact outerLeftABC_row_0_0_0
  · exact outerLeftABC_row_0_0_1
  · exact outerLeftABC_row_0_0_2
  · exact outerLeftABC_row_0_0_3
  · exact outerLeftABC_row_0_1_0
  · exact outerLeftABC_row_0_1_1
  · exact outerLeftABC_row_0_1_2
  · exact outerLeftABC_row_0_1_3
  · exact outerLeftABC_row_1_0_0
  · exact outerLeftABC_row_1_0_1
  · exact outerLeftABC_row_1_0_2
  · exact outerLeftABC_row_1_0_3
  · exact outerLeftABC_row_1_1_0
  · exact outerLeftABC_row_1_1_1
  · exact outerLeftABC_row_1_1_2
  · exact outerLeftABC_row_1_1_3
  · exact outerLeftABC_row_2_0_0
  · exact outerLeftABC_row_2_0_1
  · exact outerLeftABC_row_2_0_2
  · exact outerLeftABC_row_2_0_3
  · exact outerLeftABC_row_2_1_0
  · exact outerLeftABC_row_2_1_1
  · exact outerLeftABC_row_2_1_2
  · exact outerLeftABC_row_2_1_3
  · exact outerLeftABC_row_3_0_0
  · exact outerLeftABC_row_3_0_1
  · exact outerLeftABC_row_3_0_2
  · exact outerLeftABC_row_3_0_3
  · exact outerLeftABC_row_3_1_0
  · exact outerLeftABC_row_3_1_1
  · exact outerLeftABC_row_3_1_2
  · exact outerLeftABC_row_3_1_3

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms635
