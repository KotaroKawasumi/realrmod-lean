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
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms537
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 3 7) (LeftIndex 5 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBAC

theorem assocABC_eq : associatorZ 5 3 7 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBAC_eq

def outerABC : Matrix (LeftIndex 3 7 5) (RightIndex 5 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 3 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 5 7) (LeftIndex 3 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocABC

theorem assocBAC_eq : associatorZ 3 5 7 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocABC_eq

def innerABC : Matrix (LeftIndex 3 5 7) (LeftIndex 5 3 7) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 3 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 7 3) (RightIndex 5 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerRightBAC

theorem innerRightABC_eq : innerRightZ 5 3 7 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 34226296,
    decodeIntegerRow 16 3 1 25619864,
    decodeIntegerRow 16 3 1 8715508,
    decodeIntegerRow 16 3 1 17111948,
    decodeIntegerRow 16 3 1 16014056,
    decodeIntegerRow 16 3 1 5515144,
    decodeIntegerRow 16 3 1 26638988,
    decodeIntegerRow 16 3 1 37400308,
    decodeIntegerRow 16 3 1 17116788,
    decodeIntegerRow 16 3 1 8717068,
    decodeIntegerRow 16 3 1 25614984,
    decodeIntegerRow 16 3 1 34224616,
    decodeIntegerRow 16 3 1 37401652,
    decodeIntegerRow 16 3 1 26642892,
    decodeIntegerRow 16 3 1 5513896,
    decodeIntegerRow 16 3 1 16010184]

def inverseACB : Matrix (LeftIndex 5 7 3) (RightIndex 5 7 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 7 3 r) []).getD (rightPosition 5 7 3 s) 0

theorem inverseACB_eq : associatorInverseZ 5 7 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 5 3) (LeftIndex 5 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 7 3 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 3 7 5) (LeftIndex 3 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocABC

theorem assocBCA_eq : associatorZ 3 7 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocABC_eq

def innerRightBAC : Matrix (RightIndex 3 7 5) (RightIndex 3 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 5 7 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerRightABC_eq

def assocCAB : Matrix (RightIndex 7 5 3) (LeftIndex 7 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocBCA

theorem assocCAB_eq : associatorZ 7 5 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 7 5 3) (LeftIndex 5 3 7) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 3 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms537
