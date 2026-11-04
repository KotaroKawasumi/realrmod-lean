import RMod.BrundanEllis.StackingReferenceHexagonAtoms317
import RMod.BrundanEllis.StackingReferenceHexagonAtoms371
import RMod.BrundanEllis.StackingReferenceHexagonAtoms713
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms731
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 3 1) (LeftIndex 7 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocCAB

theorem assocABC_eq : associatorZ 7 3 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocCAB_eq

def outerABC : Matrix (LeftIndex 3 1 7) (RightIndex 7 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 3 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 7 1) (LeftIndex 3 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.assocABC

theorem assocBAC_eq : associatorZ 3 7 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.assocABC_eq

def innerABC : Matrix (LeftIndex 3 7 1) (LeftIndex 7 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms713.innerACB

theorem innerABC_eq : innerLeftZ 7 3 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms713.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 1 3) (RightIndex 7 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 3 1 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7232746,
    decodeIntegerRow 16 3 1 26126986,
    decodeIntegerRow 16 3 1 19922398,
    decodeIntegerRow 16 3 1 22074242,
    decodeIntegerRow 16 3 1 26481298,
    decodeIntegerRow 16 3 1 7114702,
    decodeIntegerRow 16 3 1 21011846,
    decodeIntegerRow 16 3 1 23111206,
    decodeIntegerRow 16 3 1 19935682,
    decodeIntegerRow 16 3 1 21011358,
    decodeIntegerRow 16 3 1 35930614,
    decodeIntegerRow 16 3 1 26485654,
    decodeIntegerRow 16 3 1 22074726,
    decodeIntegerRow 16 3 1 23124166,
    decodeIntegerRow 16 3 1 26131378,
    decodeIntegerRow 16 3 1 35812462]

def inverseACB : Matrix (LeftIndex 7 1 3) (RightIndex 7 1 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 1 3 r) []).getD (rightPosition 7 1 3 s) 0

theorem inverseACB_eq : associatorInverseZ 7 1 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 7 3) (LeftIndex 7 1 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms713.innerABC

theorem innerACB_eq : innerLeftZ 7 1 3 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms713.innerABC_eq

def assocBCA : Matrix (RightIndex 3 1 7) (LeftIndex 3 1 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocABC

theorem assocBCA_eq : associatorZ 3 1 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 1 7) (RightIndex 3 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 7 1 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 7 3) (LeftIndex 1 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBCA

theorem assocCAB_eq : associatorZ 1 7 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBCA_eq

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

def outerLeftABC : Matrix (RightIndex 1 7 3) (LeftIndex 7 3 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 7 3 r) []).getD (leftPosition 7 3 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 7 3 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms731
