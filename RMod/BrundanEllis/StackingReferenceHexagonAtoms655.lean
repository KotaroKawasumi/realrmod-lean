import RMod.BrundanEllis.StackingReferenceHexagonAtoms556
import RMod.BrundanEllis.StackingReferenceHexagonAtoms565
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms655
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 5 5) (LeftIndex 6 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocCAB

theorem assocABC_eq : associatorZ 6 5 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocCAB_eq

def outerABC : Matrix (LeftIndex 5 5 6) (RightIndex 6 5 5) ℤ :=
  (show Matrix (Fin 4 × Fin 4 × Fin 1) (Fin 4 × Fin 4 × Fin 1) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 5 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 6 5) (LeftIndex 5 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocBCA

theorem assocBAC_eq : associatorZ 5 6 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocBCA_eq

def innerABC : Matrix (LeftIndex 5 6 5) (LeftIndex 6 5 5) ℤ :=
  (show Matrix (Fin 2 × Fin 8 × Fin 1) (Fin 2 × Fin 8 × Fin 1) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 5 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 5 5) (RightIndex 6 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms565.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 5 5 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms565.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 6997060,
    decodeIntegerRow 16 3 1 26247200,
    decodeIntegerRow 16 3 1 6997552,
    decodeIntegerRow 16 3 1 16799360,
    decodeIntegerRow 16 3 1 19950880,
    decodeIntegerRow 16 3 1 22062100,
    decodeIntegerRow 16 3 1 23100160,
    decodeIntegerRow 16 3 1 22060624,
    decodeIntegerRow 16 3 1 19907140,
    decodeIntegerRow 16 3 1 22047520,
    decodeIntegerRow 16 3 1 23135152,
    decodeIntegerRow 16 3 1 22048960,
    decodeIntegerRow 16 3 1 7351840,
    decodeIntegerRow 16 3 1 26365460,
    decodeIntegerRow 16 3 1 7351360,
    decodeIntegerRow 16 3 1 16681424]

def inverseACB : Matrix (LeftIndex 6 5 5) (RightIndex 6 5 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 5 5 r) []).getD (rightPosition 6 5 5 s) 0

theorem inverseACB_eq : associatorInverseZ 6 5 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 6 5) (LeftIndex 6 5 5) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 6 5 5 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 5 5 6) (LeftIndex 5 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocABC

theorem assocBCA_eq : associatorZ 5 5 6 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocABC_eq

def innerRightBAC : Matrix (RightIndex 5 5 6) (RightIndex 5 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms565.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 6 5 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms565.innerRightABC_eq

def assocCAB : Matrix (RightIndex 5 6 5) (LeftIndex 5 6 5) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 5 6 5 = assocCAB := assocBAC_eq

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

def outerLeftABC : Matrix (RightIndex 5 6 5) (LeftIndex 6 5 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 6 5 r) []).getD (leftPosition 6 5 5 s) 0

theorem outerLeftABC_eq : outerLeftZ 6 5 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms655
