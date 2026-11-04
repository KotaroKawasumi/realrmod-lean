import RMod.BrundanEllis.StackingReferenceHexagonAtoms366
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms636
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 6 3 6) (LeftIndex 6 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBAC

theorem assocABC_eq : associatorZ 6 3 6 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBAC_eq

def outerABC : Matrix (LeftIndex 3 6 6) (RightIndex 6 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 6 3 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 3 6 6) (LeftIndex 3 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocABC

theorem assocBAC_eq : associatorZ 3 6 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocABC_eq

def innerABC : Matrix (LeftIndex 3 6 6) (LeftIndex 6 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 6 3 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 6 6 3) (RightIndex 6 3 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.innerRightBAC

theorem innerRightABC_eq : innerRightZ 6 3 6 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7889128,
    decodeIntegerRow 16 3 1 18411368,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 24631196,
    decodeIntegerRow 16 3 1 35156644,
    decodeIntegerRow 16 3 1 27859044,
    decodeIntegerRow 16 3 1 36232156,
    decodeIntegerRow 16 3 1 18253848,
    decodeIntegerRow 16 3 1 7521688,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 15183192]

def inverseACB : Matrix (LeftIndex 6 6 3) (RightIndex 6 6 3) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 6 6 3 r) []).getD (rightPosition 6 6 3 s) 0

theorem inverseACB_eq : associatorInverseZ 6 6 3 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21529921]

def innerACB : Matrix (LeftIndex 6 6 3) (LeftIndex 6 6 3) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 6 6 3 r) []).getD (leftPosition 6 6 3 s) 0

theorem innerACB_eq : innerLeftZ 6 6 3 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 3 6 6) (LeftIndex 3 6 6) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 3 6 6 = assocBCA := assocBAC_eq

def innerRightBAC : Matrix (RightIndex 3 6 6) (RightIndex 3 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.innerRightABC

theorem innerRightBAC_eq : innerRightZ 3 6 6 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.innerRightABC_eq

def assocCAB : Matrix (RightIndex 6 6 3) (LeftIndex 6 6 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBCA

theorem assocCAB_eq : associatorZ 6 6 3 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366.assocBCA_eq

def outerLeftABC : Matrix (RightIndex 6 6 3) (LeftIndex 6 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 6 3 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms636
