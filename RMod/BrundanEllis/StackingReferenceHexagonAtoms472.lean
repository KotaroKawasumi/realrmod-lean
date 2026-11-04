import RMod.BrundanEllis.StackingReferenceHexagonAtoms427
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23117764,
    decodeIntegerRow 16 3 1 20991676,
    decodeIntegerRow 16 3 1 7173724,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 21543044,
    decodeIntegerRow 16 3 1 21516796,
    decodeIntegerRow 16 3 1 21346204,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 21503678,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 21346222,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 19929118,
    decodeIntegerRow 16 3 1 20992162,
    decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 16742578]

def assocABC : Matrix (RightIndex 4 7 2) (LeftIndex 4 7 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 7 2 r) []).getD (leftPosition 4 7 2 s) 0

theorem assocABC_eq : associatorZ 4 7 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 7 2 4) (RightIndex 4 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 7 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 4 2) (LeftIndex 7 4 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocCAB

theorem assocBAC_eq : associatorZ 7 4 2 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 4 2) (LeftIndex 4 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.innerACB

theorem innerABC_eq : innerLeftZ 4 7 2 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 2 7) (RightIndex 4 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 7 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 7174480,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 26306320,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21344026]

def inverseACB : Matrix (LeftIndex 4 2 7) (RightIndex 4 2 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 2 7 r) []).getD (rightPosition 4 2 7 s) 0

theorem inverseACB_eq : associatorInverseZ 4 2 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 4 7) (LeftIndex 4 2 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.innerABC

theorem innerACB_eq : innerLeftZ 4 2 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 18153268,
    decodeIntegerRow 16 3 1 6682892,
    decodeIntegerRow 16 3 1 7626216,
    decodeIntegerRow 16 3 1 27732184,
    decodeIntegerRow 16 3 1 6603188,
    decodeIntegerRow 16 3 1 24530572,
    decodeIntegerRow 16 3 1 14977576,
    decodeIntegerRow 16 3 1 7785624,
    decodeIntegerRow 16 3 1 6681864,
    decodeIntegerRow 16 3 1 18148744,
    decodeIntegerRow 16 3 1 27727948,
    decodeIntegerRow 16 3 1 7628108,
    decodeIntegerRow 16 3 1 24526024,
    decodeIntegerRow 16 3 1 6604104,
    decodeIntegerRow 16 3 1 7783628,
    decodeIntegerRow 16 3 1 14973388]

def assocBCA : Matrix (RightIndex 7 2 4) (LeftIndex 7 2 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 2 4 r) []).getD (leftPosition 7 2 4 s) 0

theorem assocBCA_eq : associatorZ 7 2 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 2 4) (RightIndex 7 4 2) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 4 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 2 4 7) (LeftIndex 2 4 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBAC

theorem assocCAB_eq : associatorZ 2 4 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 4 7) (LeftIndex 4 7 2) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 7 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472
