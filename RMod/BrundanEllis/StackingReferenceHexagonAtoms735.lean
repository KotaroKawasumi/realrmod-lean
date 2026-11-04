import RMod.BrundanEllis.StackingReferenceHexagonAtoms357
import RMod.BrundanEllis.StackingReferenceHexagonAtoms375
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms735
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 3 5) (LeftIndex 7 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocCAB

theorem assocABC_eq : associatorZ 7 3 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocCAB_eq

def outerABC : Matrix (LeftIndex 3 5 7) (RightIndex 7 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 3 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 7 5) (LeftIndex 3 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocABC

theorem assocBAC_eq : associatorZ 3 7 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocABC_eq

def innerABC : Matrix (LeftIndex 3 7 5) (LeftIndex 7 3 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 3 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 5 3) (RightIndex 7 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 3 5 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 37466582,
    decodeIntegerRow 16 3 1 26837746,
    decodeIntegerRow 16 3 1 21365086,
    decodeIntegerRow 16 3 1 21468442,
    decodeIntegerRow 16 3 1 17271802,
    decodeIntegerRow 16 3 1 8768766,
    decodeIntegerRow 16 3 1 21587026,
    decodeIntegerRow 16 3 1 21719542,
    decodeIntegerRow 16 3 1 21590914,
    decodeIntegerRow 16 3 1 21720838,
    decodeIntegerRow 16 3 1 17271862,
    decodeIntegerRow 16 3 1 8768786,
    decodeIntegerRow 16 3 1 21680014,
    decodeIntegerRow 16 3 1 21573418,
    decodeIntegerRow 16 3 1 5580122,
    decodeIntegerRow 16 3 1 16208926]

def inverseACB : Matrix (LeftIndex 7 5 3) (RightIndex 7 5 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 5 3 r) []).getD (rightPosition 7 5 3 s) 0

theorem inverseACB_eq : associatorInverseZ 7 5 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 7 3) (LeftIndex 7 5 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 7 5 3 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 3 5 7) (LeftIndex 3 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocABC

theorem assocBCA_eq : associatorZ 3 5 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 5 7) (RightIndex 3 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 7 5 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 7 3) (LeftIndex 5 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBCA

theorem assocCAB_eq : associatorZ 5 7 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 5 7 3) (LeftIndex 7 3 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 3 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms735
