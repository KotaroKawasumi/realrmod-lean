import RMod.BrundanEllis.StackingReferenceHexagonAtoms527
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 19928956,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 22054558,
    decodeIntegerRow 16 3 1 23117602,
    decodeIntegerRow 16 3 1 26304142,
    decodeIntegerRow 16 3 1 35871538,
    decodeIntegerRow 16 3 1 21700498,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21543042,
    decodeIntegerRow 16 3 1 21516802]

def assocABC : Matrix (RightIndex 5 7 2) (LeftIndex 5 7 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 7 2 r) []).getD (leftPosition 5 7 2 s) 0

theorem assocABC_eq : associatorZ 5 7 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523441,
    decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def outerABC : Matrix (LeftIndex 7 2 5) (RightIndex 5 7 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 7 2 5 r) []).getD (rightPosition 5 7 2 s) 0

theorem outerABC_eq : outerRightZ 5 7 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 5 2) (LeftIndex 7 5 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocCAB

theorem assocBAC_eq : associatorZ 7 5 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 5 2) (LeftIndex 5 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.innerACB

theorem innerABC_eq : innerLeftZ 5 7 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 2 7) (RightIndex 5 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 7 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21050240,
    decodeIntegerRow 16 3 1 19754080,
    decodeIntegerRow 16 3 1 16746880,
    decodeIntegerRow 16 3 1 7155040,
    decodeIntegerRow 16 3 1 22114580,
    decodeIntegerRow 16 3 1 22938352,
    decodeIntegerRow 16 3 1 26312980,
    decodeIntegerRow 16 3 1 35852368,
    decodeIntegerRow 16 3 1 16733920,
    decodeIntegerRow 16 3 1 35852800,
    decodeIntegerRow 16 3 1 20933600,
    decodeIntegerRow 16 3 1 22942720,
    decodeIntegerRow 16 3 1 16747024,
    decodeIntegerRow 16 3 1 35892220,
    decodeIntegerRow 16 3 1 21051696,
    decodeIntegerRow 16 3 1 23297020]

def inverseACB : Matrix (LeftIndex 5 2 7) (RightIndex 5 2 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 2 7 r) []).getD (rightPosition 5 2 7 s) 0

theorem inverseACB_eq : associatorInverseZ 5 2 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 5 7) (LeftIndex 5 2 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.innerABC

theorem innerACB_eq : innerLeftZ 5 2 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 18520684,
    decodeIntegerRow 16 3 1 36363884,
    decodeIntegerRow 16 3 1 35420556,
    decodeIntegerRow 16 3 1 28073356,
    decodeIntegerRow 16 3 1 24893440,
    decodeIntegerRow 16 3 1 6604160,
    decodeIntegerRow 16 3 1 7783680,
    decodeIntegerRow 16 3 1 15314560,
    decodeIntegerRow 16 3 1 36443588,
    decodeIntegerRow 16 3 1 18148732,
    decodeIntegerRow 16 3 1 27727972,
    decodeIntegerRow 16 3 1 35261148,
    decodeIntegerRow 16 3 1 36364800,
    decodeIntegerRow 16 3 1 18516160,
    decodeIntegerRow 16 3 1 28069120,
    decodeIntegerRow 16 3 1 35418560]

def assocBCA : Matrix (RightIndex 7 2 5) (LeftIndex 7 2 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 2 5 r) []).getD (leftPosition 7 2 5 s) 0

theorem assocBCA_eq : associatorZ 7 2 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 2 5) (RightIndex 7 5 2) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 5 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 2 5 7) (LeftIndex 2 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBAC

theorem assocCAB_eq : associatorZ 2 5 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms527.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 5 7) (LeftIndex 5 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 7 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms572
