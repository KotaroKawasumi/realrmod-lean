import RMod.BrundanEllis.StackingReferenceHexagonAtoms517
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 6642526,
    decodeIntegerRow 16 3 1 18332446,
    decodeIntegerRow 16 3 1 27898546,
    decodeIntegerRow 16 3 1 7706866,
    decodeIntegerRow 16 3 1 21339646,
    decodeIntegerRow 16 3 1 21483966,
    decodeIntegerRow 16 3 1 21602066,
    decodeIntegerRow 16 3 1 21352786,
    decodeIntegerRow 16 3 1 21352762,
    decodeIntegerRow 16 3 1 21602118,
    decodeIntegerRow 16 3 1 21562698,
    decodeIntegerRow 16 3 1 21707062,
    decodeIntegerRow 16 3 1 7704922,
    decodeIntegerRow 16 3 1 27902758,
    decodeIntegerRow 16 3 1 24709738,
    decodeIntegerRow 16 3 1 36403222]

def assocABC : Matrix (RightIndex 5 7 1) (LeftIndex 5 7 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 7 1 r) []).getD (leftPosition 5 7 1 s) 0

theorem assocABC_eq : associatorZ 5 7 1 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 7 1 5) (RightIndex 5 7 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 7 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 5 1) (LeftIndex 7 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocCAB

theorem assocBAC_eq : associatorZ 7 5 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 5 1) (LeftIndex 5 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.innerACB

theorem innerABC_eq : innerLeftZ 5 7 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 1 7) (RightIndex 5 7 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 7 1 = innerRightABC := by
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

def inverseACB : Matrix (LeftIndex 5 1 7) (RightIndex 5 1 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 1 7 r) []).getD (rightPosition 5 1 7 s) 0

theorem inverseACB_eq : associatorInverseZ 5 1 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 5 7) (LeftIndex 5 1 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.innerABC

theorem innerACB_eq : innerLeftZ 5 1 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.innerABC_eq

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

def assocBCA : Matrix (RightIndex 7 1 5) (LeftIndex 7 1 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 1 5 r) []).getD (leftPosition 7 1 5 s) 0

theorem assocBCA_eq : associatorZ 7 1 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 1 5) (RightIndex 7 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 5 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 1 5 7) (LeftIndex 1 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBAC

theorem assocCAB_eq : associatorZ 1 5 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBAC_eq

def outerLeftABC : Matrix (RightIndex 1 5 7) (LeftIndex 5 7 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 7 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571
