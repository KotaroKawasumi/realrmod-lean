import RMod.BrundanEllis.StackingReferenceHexagonAtoms345
import RMod.BrundanEllis.StackingReferenceHexagonAtoms354
import RMod.BrundanEllis.StackingReferenceHexagonAtoms435
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms453
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 4 5 3) (LeftIndex 4 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocBCA

theorem assocABC_eq : associatorZ 4 5 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocBCA_eq

def outerABC : Matrix (LeftIndex 5 3 4) (RightIndex 4 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem outerABC_row_0_0_0 : (outerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_0 : (outerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_1 : (outerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_2 : (outerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_4_0_3 : (outerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_0 : (outerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_1 : (outerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_2 : (outerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_5_0_3 : (outerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_0 : (outerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_1 : (outerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_2 : (outerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_6_0_3 : (outerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_0 : (outerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_1 : (outerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_2 : (outerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_7_0_3 : (outerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = outerABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 4 5 3 = outerABC := by
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

def assocBAC : Matrix (RightIndex 5 4 3) (LeftIndex 5 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms354.assocBCA

theorem assocBAC_eq : associatorZ 5 4 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms354.assocBCA_eq

def innerABC : Matrix (LeftIndex 5 4 3) (LeftIndex 4 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms435.innerACB

theorem innerABC_eq : innerLeftZ 4 5 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms435.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 3 5) (RightIndex 4 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 4) (Fin 8 × Fin 1 × Fin 4) ℤ from 1)

private theorem innerRightABC_row_0_0_0 : (innerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_1 : (innerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_2 : (innerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_0_0_3 : (innerRightZ 4 5 3) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_0 : (innerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_1 : (innerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_2 : (innerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_1_0_3 : (innerRightZ 4 5 3) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_0 : (innerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_1 : (innerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_2 : (innerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_2_0_3 : (innerRightZ 4 5 3) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_0 : (innerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_1 : (innerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_2 : (innerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_3_0_3 : (innerRightZ 4 5 3) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_0 : (innerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_1 : (innerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_2 : (innerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_4_0_3 : (innerRightZ 4 5 3) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_0 : (innerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_1 : (innerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_2 : (innerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_5_0_3 : (innerRightZ 4 5 3) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_0 : (innerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_1 : (innerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_2 : (innerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_6_0_3 : (innerRightZ 4 5 3) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_0 : (innerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_1 : (innerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_2 : (innerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightABC_row_7_0_3 : (innerRightZ 4 5 3) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = innerRightABC ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightABC_eq : innerRightZ 4 5 3 = innerRightABC := by
  funext r
  fin_cases r
  · exact innerRightABC_row_0_0_0
  · exact innerRightABC_row_0_0_1
  · exact innerRightABC_row_0_0_2
  · exact innerRightABC_row_0_0_3
  · exact innerRightABC_row_1_0_0
  · exact innerRightABC_row_1_0_1
  · exact innerRightABC_row_1_0_2
  · exact innerRightABC_row_1_0_3
  · exact innerRightABC_row_2_0_0
  · exact innerRightABC_row_2_0_1
  · exact innerRightABC_row_2_0_2
  · exact innerRightABC_row_2_0_3
  · exact innerRightABC_row_3_0_0
  · exact innerRightABC_row_3_0_1
  · exact innerRightABC_row_3_0_2
  · exact innerRightABC_row_3_0_3
  · exact innerRightABC_row_4_0_0
  · exact innerRightABC_row_4_0_1
  · exact innerRightABC_row_4_0_2
  · exact innerRightABC_row_4_0_3
  · exact innerRightABC_row_5_0_0
  · exact innerRightABC_row_5_0_1
  · exact innerRightABC_row_5_0_2
  · exact innerRightABC_row_5_0_3
  · exact innerRightABC_row_6_0_0
  · exact innerRightABC_row_6_0_1
  · exact innerRightABC_row_6_0_2
  · exact innerRightABC_row_6_0_3
  · exact innerRightABC_row_7_0_0
  · exact innerRightABC_row_7_0_1
  · exact innerRightABC_row_7_0_2
  · exact innerRightABC_row_7_0_3

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 881950539463096,
    decodeIntegerRow 32 3 1 1018706872716184,
    decodeIntegerRow 32 3 1 524888147794252,
    decodeIntegerRow 32 3 1 1755144493417012,
    decodeIntegerRow 32 3 1 926510095516468,
    decodeIntegerRow 32 3 1 926510092316212,
    decodeIntegerRow 32 3 1 926510104227896,
    decodeIntegerRow 32 3 1 926510075411816,
    decodeIntegerRow 32 3 1 108015264472936,
    decodeIntegerRow 32 3 1 1348453020546616,
    decodeIntegerRow 32 3 1 1017326106093388,
    decodeIntegerRow 32 3 1 879565578932812,
    decodeIntegerRow 32 3 1 926510113675572,
    decodeIntegerRow 32 3 1 926510085096012,
    decodeIntegerRow 32 3 1 926510092284136,
    decodeIntegerRow 32 3 1 926510095461064,
    decodeIntegerRow 32 3 1 926510104228212,
    decodeIntegerRow 32 3 1 926510113439372,
    decodeIntegerRow 32 3 1 926510093338216,
    decodeIntegerRow 32 3 1 926510092310344,
    decodeIntegerRow 32 3 1 1328117749546216,
    decodeIntegerRow 32 3 1 1755172215505336,
    decodeIntegerRow 32 3 1 881821915860748,
    decodeIntegerRow 32 3 1 834562814930572,
    decodeIntegerRow 32 3 1 926510092289932,
    decodeIntegerRow 32 3 1 926510093387788,
    decodeIntegerRow 32 3 1 926510075175624,
    decodeIntegerRow 32 3 1 926510085096344,
    decodeIntegerRow 32 3 1 835441484599624,
    decodeIntegerRow 32 3 1 879688003807336,
    decodeIntegerRow 32 3 1 108043330935028,
    decodeIntegerRow 32 3 1 504553565541388]

def inverseACB : Matrix (LeftIndex 4 3 5) (RightIndex 4 3 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 3 5 r) []).getD (rightPosition 4 3 5 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_0 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_1 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_2 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_1_3 : (associatorInverseZ 4 3 5) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_0 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_1 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_2 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_1_3 : (associatorInverseZ 4 3 5) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_0 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_1 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_2 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_1_3 : (associatorInverseZ 4 3 5) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_0 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_1 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_2 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_1_3 : (associatorInverseZ 4 3 5) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = inverseACB ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 4 3 5 = inverseACB := by
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
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_1_1_0
  · exact inverseACB_row_1_1_1
  · exact inverseACB_row_1_1_2
  · exact inverseACB_row_1_1_3
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_2_1_0
  · exact inverseACB_row_2_1_1
  · exact inverseACB_row_2_1_2
  · exact inverseACB_row_2_1_3
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_3_1_0
  · exact inverseACB_row_3_1_1
  · exact inverseACB_row_3_1_2
  · exact inverseACB_row_3_1_3

def innerACB : Matrix (LeftIndex 3 4 5) (LeftIndex 4 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms435.innerABC

theorem innerACB_eq : innerLeftZ 4 3 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms435.innerABC_eq

def assocBCA : Matrix (RightIndex 5 3 4) (LeftIndex 5 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocCAB

theorem assocBCA_eq : associatorZ 5 3 4 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocCAB_eq

def innerRightBAC : Matrix (RightIndex 5 3 4) (RightIndex 5 4 3) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 4) (Fin 4 × Fin 2 × Fin 4) ℤ from 1)

private theorem innerRightBAC_row_0_0_0 : (innerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_1 : (innerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_2 : (innerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_0_3 : (innerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_0 : (innerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_1 : (innerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_2 : (innerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_0_1_3 : (innerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_0 : (innerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_1 : (innerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_2 : (innerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_0_3 : (innerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_0 : (innerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_1 : (innerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_2 : (innerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_1_1_3 : (innerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_0 : (innerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_1 : (innerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_2 : (innerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_0_3 : (innerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_0 : (innerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_1 : (innerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_2 : (innerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_2_1_3 : (innerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_0 : (innerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_1 : (innerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_2 : (innerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_0_3 : (innerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = innerRightBAC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_0 : (innerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_1 : (innerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_2 : (innerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem innerRightBAC_row_3_1_3 : (innerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = innerRightBAC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem innerRightBAC_eq : innerRightZ 5 4 3 = innerRightBAC := by
  funext r
  fin_cases r
  · exact innerRightBAC_row_0_0_0
  · exact innerRightBAC_row_0_0_1
  · exact innerRightBAC_row_0_0_2
  · exact innerRightBAC_row_0_0_3
  · exact innerRightBAC_row_0_1_0
  · exact innerRightBAC_row_0_1_1
  · exact innerRightBAC_row_0_1_2
  · exact innerRightBAC_row_0_1_3
  · exact innerRightBAC_row_1_0_0
  · exact innerRightBAC_row_1_0_1
  · exact innerRightBAC_row_1_0_2
  · exact innerRightBAC_row_1_0_3
  · exact innerRightBAC_row_1_1_0
  · exact innerRightBAC_row_1_1_1
  · exact innerRightBAC_row_1_1_2
  · exact innerRightBAC_row_1_1_3
  · exact innerRightBAC_row_2_0_0
  · exact innerRightBAC_row_2_0_1
  · exact innerRightBAC_row_2_0_2
  · exact innerRightBAC_row_2_0_3
  · exact innerRightBAC_row_2_1_0
  · exact innerRightBAC_row_2_1_1
  · exact innerRightBAC_row_2_1_2
  · exact innerRightBAC_row_2_1_3
  · exact innerRightBAC_row_3_0_0
  · exact innerRightBAC_row_3_0_1
  · exact innerRightBAC_row_3_0_2
  · exact innerRightBAC_row_3_0_3
  · exact innerRightBAC_row_3_1_0
  · exact innerRightBAC_row_3_1_1
  · exact innerRightBAC_row_3_1_2
  · exact innerRightBAC_row_3_1_3

def assocCAB : Matrix (RightIndex 3 4 5) (LeftIndex 3 4 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocABC

theorem assocCAB_eq : associatorZ 3 4 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
    decodeIntegerRow 32 3 1 926510094425923,
    decodeIntegerRow 32 3 1 926510094425929,
    decodeIntegerRow 32 3 1 926510094425947,
    decodeIntegerRow 32 3 1 926510094426001,
    decodeIntegerRow 32 3 1 926510094426163,
    decodeIntegerRow 32 3 1 926510094426649,
    decodeIntegerRow 32 3 1 926510094428107,
    decodeIntegerRow 32 3 1 926510094432481,
    decodeIntegerRow 32 3 1 926510094445603,
    decodeIntegerRow 32 3 1 926510094484969,
    decodeIntegerRow 32 3 1 926510094603067,
    decodeIntegerRow 32 3 1 926510094957361,
    decodeIntegerRow 32 3 1 926510096020243,
    decodeIntegerRow 32 3 1 926510099208889,
    decodeIntegerRow 32 3 1 926510108774827,
    decodeIntegerRow 32 3 1 926510051379199,
    decodeIntegerRow 32 3 1 926509965285757,
    decodeIntegerRow 32 3 1 926509707005431,
    decodeIntegerRow 32 3 1 926508932164453,
    decodeIntegerRow 32 3 1 926506607641519,
    decodeIntegerRow 32 3 1 926499634072717,
    decodeIntegerRow 32 3 1 926478713366311,
    decodeIntegerRow 32 3 1 926415951247093,
    decodeIntegerRow 32 3 1 926227664889439,
    decodeIntegerRow 32 3 1 925662805816477,
    decodeIntegerRow 32 3 1 923968228597591,
    decodeIntegerRow 32 3 1 918884496940933,
    decodeIntegerRow 32 3 1 903633301970959,
    decodeIntegerRow 32 3 1 857879717061037,
    decodeIntegerRow 32 3 1 720618962331271,
    decodeIntegerRow 32 3 1 308836698141973]

def outerLeftABC : Matrix (RightIndex 3 4 5) (LeftIndex 4 5 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 4 5 r) []).getD (leftPosition 4 5 3 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 4 5 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 4 5 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 4 5 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 4 5 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 4 5 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 4 5 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 4 5 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 4 5 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 4 5 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 4 5 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 4 5 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 4 5 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 4 5 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 4 5 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 4 5 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 4 5 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 4 5 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 4 5 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 4 5 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 4 5 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 4 5 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 4 5 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 4 5 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 4 5 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 4 5 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 4 5 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 4 5 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 4 5 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 4 5 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 4 5 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 4 5 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 4 5 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 4 5 3 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms453
