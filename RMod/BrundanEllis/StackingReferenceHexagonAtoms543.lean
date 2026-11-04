import RMod.BrundanEllis.StackingReferenceHexagonAtoms345
import RMod.BrundanEllis.StackingReferenceHexagonAtoms354
import RMod.BrundanEllis.StackingReferenceHexagonAtoms453
import RMod.BrundanEllis.StackingReferenceHexagonAtoms534
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms543
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 4 3) (LeftIndex 5 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms354.assocBCA

theorem assocABC_eq : associatorZ 5 4 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms354.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 32 3 1 926510094425921,
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

def outerABC : Matrix (LeftIndex 4 3 5) (RightIndex 5 4 3) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 4 3 5 r) []).getD (rightPosition 5 4 3 s) 0

private theorem outerABC_row_0_0_0 : (outerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_1 : (outerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_2 : (outerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_0_3 : (outerRightZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_0 : (outerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_1 : (outerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_2 : (outerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_0_1_3 : (outerRightZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_0 : (outerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_1 : (outerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_2 : (outerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_0_3 : (outerRightZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_0 : (outerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_1 : (outerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_2 : (outerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_1_1_3 : (outerRightZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_0 : (outerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_1 : (outerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_2 : (outerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_0_3 : (outerRightZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_0 : (outerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_1 : (outerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_2 : (outerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_2_1_3 : (outerRightZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_0 : (outerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_1 : (outerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_2 : (outerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_0_3 : (outerRightZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_0 : (outerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_1 : (outerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_2 : (outerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerABC_row_3_1_3 : (outerRightZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerABC_eq : outerRightZ 5 4 3 = outerABC := by
  funext r
  fin_cases r
  · exact outerABC_row_0_0_0
  · exact outerABC_row_0_0_1
  · exact outerABC_row_0_0_2
  · exact outerABC_row_0_0_3
  · exact outerABC_row_0_1_0
  · exact outerABC_row_0_1_1
  · exact outerABC_row_0_1_2
  · exact outerABC_row_0_1_3
  · exact outerABC_row_1_0_0
  · exact outerABC_row_1_0_1
  · exact outerABC_row_1_0_2
  · exact outerABC_row_1_0_3
  · exact outerABC_row_1_1_0
  · exact outerABC_row_1_1_1
  · exact outerABC_row_1_1_2
  · exact outerABC_row_1_1_3
  · exact outerABC_row_2_0_0
  · exact outerABC_row_2_0_1
  · exact outerABC_row_2_0_2
  · exact outerABC_row_2_0_3
  · exact outerABC_row_2_1_0
  · exact outerABC_row_2_1_1
  · exact outerABC_row_2_1_2
  · exact outerABC_row_2_1_3
  · exact outerABC_row_3_0_0
  · exact outerABC_row_3_0_1
  · exact outerABC_row_3_0_2
  · exact outerABC_row_3_0_3
  · exact outerABC_row_3_1_0
  · exact outerABC_row_3_1_1
  · exact outerABC_row_3_1_2
  · exact outerABC_row_3_1_3

def assocBAC : Matrix (RightIndex 4 5 3) (LeftIndex 4 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocBCA

theorem assocBAC_eq : associatorZ 4 5 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocBCA_eq

def innerABC : Matrix (LeftIndex 4 5 3) (LeftIndex 5 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms534.innerACB

theorem innerABC_eq : innerLeftZ 5 4 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms534.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 3 4) (RightIndex 5 4 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms453.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 4 3 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms453.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 32 3 1 921426274552972,
    decodeIntegerRow 32 3 1 916342802235148,
    decodeIntegerRow 32 3 1 927074159525704,
    decodeIntegerRow 32 3 1 927641352688024,
    decodeIntegerRow 32 3 1 936677730987544,
    decodeIntegerRow 32 3 1 921426446734024,
    decodeIntegerRow 32 3 1 925381935528052,
    decodeIntegerRow 32 3 1 927075709208308,
    decodeIntegerRow 32 3 1 925381916395852,
    decodeIntegerRow 32 3 1 925944441380428,
    decodeIntegerRow 32 3 1 916342459987144,
    decodeIntegerRow 32 3 1 921426450991384,
    decodeIntegerRow 32 3 1 925945991061736,
    decodeIntegerRow 32 3 1 927641371819576,
    decodeIntegerRow 32 3 1 921426278798668,
    decodeIntegerRow 32 3 1 936677384488012,
    decodeIntegerRow 32 3 1 514720856694028,
    decodeIntegerRow 32 3 1 102959513198068,
    decodeIntegerRow 32 3 1 972200917452824,
    decodeIntegerRow 32 3 1 1018142788602296,
    decodeIntegerRow 32 3 1 102931618922824,
    decodeIntegerRow 32 3 1 1338285385020136,
    decodeIntegerRow 32 3 1 1017891740125428,
    decodeIntegerRow 32 3 1 880693747160588,
    decodeIntegerRow 32 3 1 1017891739889228,
    decodeIntegerRow 32 3 1 972326441218868,
    decodeIntegerRow 32 3 1 1750088569955224,
    decodeIntegerRow 32 3 1 1338285385072696,
    decodeIntegerRow 32 3 1 880819271871416,
    decodeIntegerRow 32 3 1 1018142788366104,
    decodeIntegerRow 32 3 1 514720856641612,
    decodeIntegerRow 32 3 1 1750060675680052]

def inverseACB : Matrix (LeftIndex 5 3 4) (RightIndex 5 3 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 3 4 r) []).getD (rightPosition 5 3 4 s) 0

private theorem inverseACB_row_0_0_0 : (associatorInverseZ 5 3 4) ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_1 : (associatorInverseZ 5 3 4) ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_2 : (associatorInverseZ 5 3 4) ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_0_0_3 : (associatorInverseZ 5 3 4) ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((0 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_0 : (associatorInverseZ 5 3 4) ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_1 : (associatorInverseZ 5 3 4) ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_2 : (associatorInverseZ 5 3 4) ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_1_0_3 : (associatorInverseZ 5 3 4) ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((1 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_0 : (associatorInverseZ 5 3 4) ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_1 : (associatorInverseZ 5 3 4) ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_2 : (associatorInverseZ 5 3 4) ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_2_0_3 : (associatorInverseZ 5 3 4) ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((2 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_0 : (associatorInverseZ 5 3 4) ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_1 : (associatorInverseZ 5 3 4) ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_2 : (associatorInverseZ 5 3 4) ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_3_0_3 : (associatorInverseZ 5 3 4) ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((3 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_0 : (associatorInverseZ 5 3 4) ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_1 : (associatorInverseZ 5 3 4) ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_2 : (associatorInverseZ 5 3 4) ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_4_0_3 : (associatorInverseZ 5 3 4) ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((4 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_0 : (associatorInverseZ 5 3 4) ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_1 : (associatorInverseZ 5 3 4) ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_2 : (associatorInverseZ 5 3 4) ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_5_0_3 : (associatorInverseZ 5 3 4) ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((5 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_0 : (associatorInverseZ 5 3 4) ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_1 : (associatorInverseZ 5 3 4) ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_2 : (associatorInverseZ 5 3 4) ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_6_0_3 : (associatorInverseZ 5 3 4) ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((6 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_0 : (associatorInverseZ 5 3 4) ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_1 : (associatorInverseZ 5 3 4) ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_2 : (associatorInverseZ 5 3 4) ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem inverseACB_row_7_0_3 : (associatorInverseZ 5 3 4) ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) = inverseACB ((7 : Fin 8), (0 : Fin 1), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem inverseACB_eq : associatorInverseZ 5 3 4 = inverseACB := by
  funext r
  fin_cases r
  · exact inverseACB_row_0_0_0
  · exact inverseACB_row_0_0_1
  · exact inverseACB_row_0_0_2
  · exact inverseACB_row_0_0_3
  · exact inverseACB_row_1_0_0
  · exact inverseACB_row_1_0_1
  · exact inverseACB_row_1_0_2
  · exact inverseACB_row_1_0_3
  · exact inverseACB_row_2_0_0
  · exact inverseACB_row_2_0_1
  · exact inverseACB_row_2_0_2
  · exact inverseACB_row_2_0_3
  · exact inverseACB_row_3_0_0
  · exact inverseACB_row_3_0_1
  · exact inverseACB_row_3_0_2
  · exact inverseACB_row_3_0_3
  · exact inverseACB_row_4_0_0
  · exact inverseACB_row_4_0_1
  · exact inverseACB_row_4_0_2
  · exact inverseACB_row_4_0_3
  · exact inverseACB_row_5_0_0
  · exact inverseACB_row_5_0_1
  · exact inverseACB_row_5_0_2
  · exact inverseACB_row_5_0_3
  · exact inverseACB_row_6_0_0
  · exact inverseACB_row_6_0_1
  · exact inverseACB_row_6_0_2
  · exact inverseACB_row_6_0_3
  · exact inverseACB_row_7_0_0
  · exact inverseACB_row_7_0_1
  · exact inverseACB_row_7_0_2
  · exact inverseACB_row_7_0_3

def innerACB : Matrix (LeftIndex 3 5 4) (LeftIndex 5 3 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms534.innerABC

theorem innerACB_eq : innerLeftZ 5 3 4 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms534.innerABC_eq

def assocBCA : Matrix (RightIndex 4 3 5) (LeftIndex 4 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocBAC

theorem assocBCA_eq : associatorZ 4 3 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms345.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 4 3 5) (RightIndex 4 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms453.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 5 3 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms453.innerRightABC_eq

def assocCAB : Matrix (RightIndex 3 5 4) (LeftIndex 3 5 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms354.assocABC

theorem assocCAB_eq : associatorZ 3 5 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms354.assocABC_eq

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

def outerLeftABC : Matrix (RightIndex 3 5 4) (LeftIndex 5 4 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 5 4 r) []).getD (leftPosition 5 4 3 s) 0

private theorem outerLeftABC_row_0_0_0 : (outerLeftZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_1 : (outerLeftZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_2 : (outerLeftZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_0_3 : (outerLeftZ 5 4 3) ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_0 : (outerLeftZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_1 : (outerLeftZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_2 : (outerLeftZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_0_1_3 : (outerLeftZ 5 4 3) ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((0 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_0 : (outerLeftZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_1 : (outerLeftZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_2 : (outerLeftZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_0_3 : (outerLeftZ 5 4 3) ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_0 : (outerLeftZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_1 : (outerLeftZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_2 : (outerLeftZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_1_1_3 : (outerLeftZ 5 4 3) ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((1 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_0 : (outerLeftZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_1 : (outerLeftZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_2 : (outerLeftZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_0_3 : (outerLeftZ 5 4 3) ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_0 : (outerLeftZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_1 : (outerLeftZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_2 : (outerLeftZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_2_1_3 : (outerLeftZ 5 4 3) ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((2 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_0 : (outerLeftZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_1 : (outerLeftZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_2 : (outerLeftZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_0_3 : (outerLeftZ 5 4 3) ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (0 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_0 : (outerLeftZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (0 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_1 : (outerLeftZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (1 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_2 : (outerLeftZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (2 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

private theorem outerLeftABC_row_3_1_3 : (outerLeftZ 5 4 3) ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) = outerLeftABC ((3 : Fin 4), (1 : Fin 2), (3 : Fin 4)) := by
  apply tripleRowCheck_sound
  decide +kernel

theorem outerLeftABC_eq : outerLeftZ 5 4 3 = outerLeftABC := by
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

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms543
