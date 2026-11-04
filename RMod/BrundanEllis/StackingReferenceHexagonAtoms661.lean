import RMod.BrundanEllis.StackingReferenceHexagonAtoms616
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms661
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 6 1) (LeftIndex 6 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.assocCAB

theorem assocABC_eq : associatorZ 6 6 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.assocCAB_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523874,
    decodeIntegerRow 16 3 1 21525622,
    decodeIntegerRow 16 3 1 21525478,
    decodeIntegerRow 16 3 1 21522414,
    decodeIntegerRow 16 3 1 21525634,
    decodeIntegerRow 16 3 1 21522902,
    decodeIntegerRow 16 3 1 21524358,
    decodeIntegerRow 16 3 1 21525454,
    decodeIntegerRow 16 3 1 24895714,
    decodeIntegerRow 16 3 1 36364342,
    decodeIntegerRow 16 3 1 35419558,
    decodeIntegerRow 16 3 1 15316654,
    decodeIntegerRow 16 3 1 36443074,
    decodeIntegerRow 16 3 1 18518422,
    decodeIntegerRow 16 3 1 28071238,
    decodeIntegerRow 16 3 1 35262094]

def outerABC : Matrix (LeftIndex 6 1 6) (RightIndex 6 6 1) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 1 6 r) []).getD (rightPosition 6 6 1 s) 0

theorem outerABC_eq : outerRightZ 6 6 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 6 1) (LeftIndex 6 6 1) ℤ := assocABC

theorem assocBAC_eq : associatorZ 6 6 1 = assocBAC := assocABC_eq

def innerABC : Matrix (LeftIndex 6 6 1) (LeftIndex 6 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.innerACB

theorem innerABC_eq : innerLeftZ 6 6 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.innerACB_eq

def innerRightABC : Matrix (RightIndex 6 1 6) (RightIndex 6 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 6 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21995024,
    decodeIntegerRow 16 3 1 20104000,
    decodeIntegerRow 16 3 1 16733920,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 35852800,
    decodeIntegerRow 16 3 1 20933600,
    decodeIntegerRow 16 3 1 23297020,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 7194352,
    decodeIntegerRow 16 3 1 22114580,
    decodeIntegerRow 16 3 1 23292640,
    decodeIntegerRow 16 3 1 21996480,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 26312980,
    decodeIntegerRow 16 3 1 35891680]

def inverseACB : Matrix (LeftIndex 6 1 6) (RightIndex 6 1 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 1 6 r) []).getD (rightPosition 6 1 6 s) 0

theorem inverseACB_eq : associatorInverseZ 6 1 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 6 6) (LeftIndex 6 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.innerABC

theorem innerACB_eq : innerLeftZ 6 1 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.innerABC_eq

def assocBCA : Matrix (RightIndex 6 1 6) (LeftIndex 6 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.assocABC

theorem assocBCA_eq : associatorZ 6 1 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.assocABC_eq

def innerRightBAC : Matrix (RightIndex 6 1 6) (RightIndex 6 6 1) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 6 1 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 6 6) (LeftIndex 1 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.assocBAC

theorem assocCAB_eq : associatorZ 1 6 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms616.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 1 6 6) (LeftIndex 6 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 6 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms661
