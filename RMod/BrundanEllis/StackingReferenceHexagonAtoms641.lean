import RMod.BrundanEllis.StackingReferenceHexagonAtoms416
import RMod.BrundanEllis.StackingReferenceHexagonAtoms461
import RMod.BrundanEllis.StackingReferenceHexagonAtoms614
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms641
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 4 1) (LeftIndex 6 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocCAB

theorem assocABC_eq : associatorZ 6 4 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocCAB_eq

def outerABC : Matrix (LeftIndex 4 1 6) (RightIndex 6 4 1) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 4 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 6 1) (LeftIndex 4 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.assocABC

theorem assocBAC_eq : associatorZ 4 6 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.assocABC_eq

def innerABC : Matrix (LeftIndex 4 6 1) (LeftIndex 6 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms614.innerACB

theorem innerABC_eq : innerLeftZ 6 4 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms614.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 1 4) (RightIndex 6 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 4 1 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 36402736,
    decodeIntegerRow 16 3 1 15143800,
    decodeIntegerRow 16 3 1 18336820,
    decodeIntegerRow 16 3 1 35341312,
    decodeIntegerRow 16 3 1 21339664,
    decodeIntegerRow 16 3 1 21602120,
    decodeIntegerRow 16 3 1 21562700,
    decodeIntegerRow 16 3 1 21352768,
    decodeIntegerRow 16 3 1 21693940,
    decodeIntegerRow 16 3 1 21562752,
    decodeIntegerRow 16 3 1 21444656,
    decodeIntegerRow 16 3 1 21339640,
    decodeIntegerRow 16 3 1 35340340,
    decodeIntegerRow 16 3 1 24714112,
    decodeIntegerRow 16 3 1 15148336,
    decodeIntegerRow 16 3 1 6642040]

def inverseACB : Matrix (LeftIndex 6 1 4) (RightIndex 6 1 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 1 4 r) []).getD (rightPosition 6 1 4 s) 0

theorem inverseACB_eq : associatorInverseZ 6 1 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 6 4) (LeftIndex 6 1 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms614.innerABC

theorem innerACB_eq : innerLeftZ 6 1 4 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms614.innerABC_eq

def assocBCA : Matrix (RightIndex 4 1 6) (LeftIndex 4 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocABC

theorem assocBCA_eq : associatorZ 4 1 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 1 6) (RightIndex 4 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 6 1 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461.innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 6 4) (LeftIndex 1 6 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBCA

theorem assocCAB_eq : associatorZ 1 6 4 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBCA_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522848,
    decodeIntegerRow 16 3 1 21521248,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521260,
    decodeIntegerRow 16 3 1 21522900,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 6721744,
    decodeIntegerRow 16 3 1 15329776,
    decodeIntegerRow 16 3 1 7745260,
    decodeIntegerRow 16 3 1 18505300,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 36482440]

def outerLeftABC : Matrix (RightIndex 1 6 4) (LeftIndex 6 4 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 6 4 r) []).getD (leftPosition 6 4 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 4 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms641
