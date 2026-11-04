import RMod.BrundanEllis.StackingReferenceHexagonAtoms315
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 17217376,
    decodeIntegerRow 16 3 1 8611968,
    decodeIntegerRow 16 3 1 26905840,
    decodeIntegerRow 16 3 1 37662600,
    decodeIntegerRow 16 3 1 37270560,
    decodeIntegerRow 16 3 1 16276960,
    decodeIntegerRow 16 3 1 34121120,
    decodeIntegerRow 16 3 1 17326240,
    decodeIntegerRow 16 3 1 8610656,
    decodeIntegerRow 16 3 1 25825408,
    decodeIntegerRow 16 3 1 37664240,
    decodeIntegerRow 16 3 1 16145800,
    decodeIntegerRow 16 3 1 16272160,
    decodeIntegerRow 16 3 1 5777760,
    decodeIntegerRow 16 3 1 17322400,
    decodeIntegerRow 16 3 1 8926880]

def assocABC : Matrix (RightIndex 3 5 1) (LeftIndex 3 5 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 5 1 r) []).getD (leftPosition 3 5 1 s) 0

theorem assocABC_eq : associatorZ 3 5 1 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 5 1 3) (RightIndex 3 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 5 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 3 1) (LeftIndex 5 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocCAB

theorem assocBAC_eq : associatorZ 5 3 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocCAB_eq

def innerABC : Matrix (LeftIndex 5 3 1) (LeftIndex 3 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.innerACB

theorem innerABC_eq : innerLeftZ 3 5 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 1 5) (RightIndex 3 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 5 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21582406,
    decodeIntegerRow 16 3 1 21700508,
    decodeIntegerRow 16 3 1 7174372,
    decodeIntegerRow 16 3 1 26306086,
    decodeIntegerRow 16 3 1 21503686,
    decodeIntegerRow 16 3 1 21529948,
    decodeIntegerRow 16 3 1 22056988,
    decodeIntegerRow 16 3 1 23116954,
    decodeIntegerRow 16 3 1 20994106,
    decodeIntegerRow 16 3 1 19928308,
    decodeIntegerRow 16 3 1 21543052,
    decodeIntegerRow 16 3 1 21516826,
    decodeIntegerRow 16 3 1 7174534,
    decodeIntegerRow 16 3 1 26306572,
    decodeIntegerRow 16 3 1 21582412,
    decodeIntegerRow 16 3 1 21700506]

def inverseACB : Matrix (LeftIndex 3 1 5) (RightIndex 3 1 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 1 5 r) []).getD (rightPosition 3 1 5 s) 0

theorem inverseACB_eq : associatorInverseZ 3 1 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 3 5) (LeftIndex 3 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.innerABC

theorem innerACB_eq : innerLeftZ 3 1 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21464314,
    decodeIntegerRow 16 3 1 21346212,
    decodeIntegerRow 16 3 1 35872348,
    decodeIntegerRow 16 3 1 16740634,
    decodeIntegerRow 16 3 1 21543034,
    decodeIntegerRow 16 3 1 21516772,
    decodeIntegerRow 16 3 1 20989732,
    decodeIntegerRow 16 3 1 19929766,
    decodeIntegerRow 16 3 1 22052614,
    decodeIntegerRow 16 3 1 23118412,
    decodeIntegerRow 16 3 1 21503668,
    decodeIntegerRow 16 3 1 21529894,
    decodeIntegerRow 16 3 1 35872186,
    decodeIntegerRow 16 3 1 16740148,
    decodeIntegerRow 16 3 1 21464308,
    decodeIntegerRow 16 3 1 21346214]

def assocBCA : Matrix (RightIndex 5 1 3) (LeftIndex 5 1 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 5 1 3 r) []).getD (leftPosition 5 1 3 s) 0

theorem assocBCA_eq : associatorZ 5 1 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 5 1 3) (RightIndex 5 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 5 3 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 1 3 5) (LeftIndex 1 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBAC

theorem assocCAB_eq : associatorZ 1 3 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 1 3 5) (LeftIndex 3 5 1) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 5 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351
