import RMod.BrundanEllis.StackingReferenceHexagonAtoms316
import RMod.BrundanEllis.StackingReferenceHexagonAtoms361
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms613
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 1 3) (LeftIndex 6 1 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.assocBCA

theorem assocABC_eq : associatorZ 6 1 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.assocBCA_eq

def outerABC : Matrix (LeftIndex 1 3 6) (RightIndex 6 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 1 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 1 6 3) (LeftIndex 1 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBCA

theorem assocBAC_eq : associatorZ 1 6 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBCA_eq

def innerABC : Matrix (LeftIndex 1 6 3) (LeftIndex 6 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 1 3 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 3 1) (RightIndex 6 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 6 1 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 35872240,
    decodeIntegerRow 16 3 1 16740400,
    decodeIntegerRow 16 3 1 26306338,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 23117686,
    decodeIntegerRow 16 3 1 21465040,
    decodeIntegerRow 16 3 1 21698320,
    decodeIntegerRow 16 3 1 21529840,
    decodeIntegerRow 16 3 1 21503920,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21530002,
    decodeIntegerRow 16 3 1 21344026,
    decodeIntegerRow 16 3 1 21583138]

def inverseACB : Matrix (LeftIndex 6 3 1) (RightIndex 6 3 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 3 1 r) []).getD (rightPosition 6 3 1 s) 0

theorem inverseACB_eq : associatorInverseZ 6 3 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 6 1) (LeftIndex 6 3 1) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 6 3 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 3 6) (LeftIndex 1 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBAC

theorem assocBCA_eq : associatorZ 1 3 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms316.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 1 3 6) (RightIndex 1 6 3) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 6 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 3 6 1) (LeftIndex 3 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.assocABC

theorem assocCAB_eq : associatorZ 3 6 1 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms361.assocABC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def outerLeftABC : Matrix (RightIndex 3 6 1) (LeftIndex 6 1 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 6 1 r) []).getD (leftPosition 6 1 3 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 1 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms613
