import RMod.BrundanEllis.StackingReferenceHexagonAtoms315
import RMod.BrundanEllis.StackingReferenceHexagonAtoms351
import RMod.BrundanEllis.StackingReferenceHexagonAtoms513
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms531
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 3 1) (LeftIndex 5 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocCAB

theorem assocABC_eq : associatorZ 5 3 1 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocCAB_eq

def outerABC : Matrix (LeftIndex 3 1 5) (RightIndex 5 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 3 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 5 1) (LeftIndex 3 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.assocABC

theorem assocBAC_eq : associatorZ 3 5 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.assocABC_eq

def innerABC : Matrix (LeftIndex 3 5 1) (LeftIndex 5 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms513.innerACB

theorem innerABC_eq : innerLeftZ 5 3 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms513.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 1 3) (RightIndex 5 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 3 1 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 21700264,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 22054810]

def inverseACB : Matrix (LeftIndex 5 1 3) (RightIndex 5 1 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 1 3 r) []).getD (rightPosition 5 1 3 s) 0

theorem inverseACB_eq : associatorInverseZ 5 1 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 5 3) (LeftIndex 5 1 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms513.innerABC

theorem innerACB_eq : innerLeftZ 5 1 3 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms513.innerABC_eq

def assocBCA : Matrix (RightIndex 3 1 5) (LeftIndex 3 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocABC

theorem assocBCA_eq : associatorZ 3 1 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 1 5) (RightIndex 3 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 5 1 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.innerRightABC_eq

def assocCAB : Matrix (RightIndex 1 5 3) (LeftIndex 1 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBCA

theorem assocCAB_eq : associatorZ 1 5 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 1 5 3) (LeftIndex 5 3 1) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 3 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms531
