import RMod.BrundanEllis.StackingReferenceHexagonAtoms357
import RMod.BrundanEllis.StackingReferenceHexagonAtoms375
import RMod.BrundanEllis.StackingReferenceHexagonAtoms537
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms573
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 7 3) (LeftIndex 5 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBCA

theorem assocABC_eq : associatorZ 5 7 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBCA_eq

def outerABC : Matrix (LeftIndex 7 3 5) (RightIndex 5 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 7 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 5 3) (LeftIndex 7 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocBCA

theorem assocBAC_eq : associatorZ 7 5 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocBCA_eq

def innerABC : Matrix (LeftIndex 7 5 3) (LeftIndex 5 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms537.innerACB

theorem innerABC_eq : innerLeftZ 5 7 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms537.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 3 7) (RightIndex 5 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 7 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 25934304,
    decodeIntegerRow 16 3 1 34331104,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 17427360,
    decodeIntegerRow 16 3 1 8820640,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680]

def inverseACB : Matrix (LeftIndex 5 3 7) (RightIndex 5 3 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 3 7 r) []).getD (rightPosition 5 3 7 s) 0

theorem inverseACB_eq : associatorInverseZ 5 3 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 5 7) (LeftIndex 5 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms537.innerABC

theorem innerACB_eq : innerLeftZ 5 3 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms537.innerABC_eq

def assocBCA : Matrix (RightIndex 7 3 5) (LeftIndex 7 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocCAB

theorem assocBCA_eq : associatorZ 7 3 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocCAB_eq

def innerRightBAC : Matrix (RightIndex 7 3 5) (RightIndex 7 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 5 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 3 5 7) (LeftIndex 3 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocABC

theorem assocCAB_eq : associatorZ 3 5 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 5 7) (LeftIndex 5 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 7 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms573
