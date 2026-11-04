import RMod.BrundanEllis.StackingReferenceHexagonAtoms357
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 34226296,
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

def assocABC : Matrix (RightIndex 3 7 5) (LeftIndex 3 7 5) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 7 5 r) []).getD (leftPosition 3 7 5 s) 0

theorem assocABC_eq : associatorZ 3 7 5 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 7 5 3) (RightIndex 3 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 7 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 3 5) (LeftIndex 7 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocCAB

theorem assocBAC_eq : associatorZ 7 3 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 3 5) (LeftIndex 3 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerACB

theorem innerABC_eq : innerLeftZ 3 7 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 5 7) (RightIndex 3 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 7 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
    decodeIntegerRow 16 3 1 35931238,
    decodeIntegerRow 16 3 1 16917294,
    decodeIntegerRow 16 3 1 7233418,
    decodeIntegerRow 16 3 1 20974414,
    decodeIntegerRow 16 3 1 19923178,
    decodeIntegerRow 16 3 1 21009406,
    decodeIntegerRow 16 3 1 19934842,
    decodeIntegerRow 16 3 1 19936354,
    decodeIntegerRow 16 3 1 21013798,
    decodeIntegerRow 16 3 1 23124946,
    decodeIntegerRow 16 3 1 22076662,
    decodeIntegerRow 16 3 1 7233586,
    decodeIntegerRow 16 3 1 16917782,
    decodeIntegerRow 16 3 1 7115326,
    decodeIntegerRow 16 3 1 16563002]

def inverseACB : Matrix (LeftIndex 3 5 7) (RightIndex 3 5 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 5 7 r) []).getD (rightPosition 3 5 7 s) 0

theorem inverseACB_eq : associatorInverseZ 3 5 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 3 7) (LeftIndex 3 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerABC

theorem innerACB_eq : innerLeftZ 3 5 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 26483234,
    decodeIntegerRow 16 3 1 35931238,
    decodeIntegerRow 16 3 1 16917294,
    decodeIntegerRow 16 3 1 7233418,
    decodeIntegerRow 16 3 1 20974414,
    decodeIntegerRow 16 3 1 19923178,
    decodeIntegerRow 16 3 1 21009406,
    decodeIntegerRow 16 3 1 19934842,
    decodeIntegerRow 16 3 1 19936354,
    decodeIntegerRow 16 3 1 21013798,
    decodeIntegerRow 16 3 1 23124946,
    decodeIntegerRow 16 3 1 22076662,
    decodeIntegerRow 16 3 1 7233586,
    decodeIntegerRow 16 3 1 16917782,
    decodeIntegerRow 16 3 1 7115326,
    decodeIntegerRow 16 3 1 16563002]

def assocBCA : Matrix (RightIndex 7 5 3) (LeftIndex 7 5 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 5 3 r) []).getD (leftPosition 7 5 3 s) 0

theorem assocBCA_eq : associatorZ 7 5 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 5 3) (RightIndex 7 3 5) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 3 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 3 7) (LeftIndex 5 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBAC

theorem assocCAB_eq : associatorZ 5 3 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 5 3 7) (LeftIndex 3 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 7 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375
