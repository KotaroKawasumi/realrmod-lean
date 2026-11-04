import RMod.BrundanEllis.StackingReferenceHexagonAtoms357
import RMod.BrundanEllis.StackingReferenceHexagonAtoms375
import RMod.BrundanEllis.StackingReferenceHexagonAtoms573
import RMod.BrundanEllis.StackingReferenceHexagonAtoms735
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms753
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 5 3) (LeftIndex 7 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocBCA

theorem assocABC_eq : associatorZ 7 5 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocBCA_eq

def outerABC : Matrix (LeftIndex 5 3 7) (RightIndex 7 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 5 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 5 7 3) (LeftIndex 5 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBCA

theorem assocBAC_eq : associatorZ 5 7 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBCA_eq

def innerABC : Matrix (LeftIndex 5 7 3) (LeftIndex 7 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms735.innerACB

theorem innerABC_eq : innerLeftZ 7 5 3 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms735.innerACB_eq

def innerRightABC : Matrix (RightIndex 7 3 5) (RightIndex 7 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms573.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 5 3 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms573.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 16263412,
    decodeIntegerRow 16 3 1 5738252,
    decodeIntegerRow 16 3 1 17339896,
    decodeIntegerRow 16 3 1 8966424,
    decodeIntegerRow 16 3 1 8571144,
    decodeIntegerRow 16 3 1 17203816,
    decodeIntegerRow 16 3 1 5422028,
    decodeIntegerRow 16 3 1 16154548,
    decodeIntegerRow 16 3 1 5736936,
    decodeIntegerRow 16 3 1 16259464,
    decodeIntegerRow 16 3 1 8964788,
    decodeIntegerRow 16 3 1 17334988,
    decodeIntegerRow 16 3 1 17208628,
    decodeIntegerRow 16 3 1 8572748,
    decodeIntegerRow 16 3 1 16158376,
    decodeIntegerRow 16 3 1 5423304]

def inverseACB : Matrix (LeftIndex 7 3 5) (RightIndex 7 3 5) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 3 5 r) []).getD (rightPosition 7 3 5 s) 0

theorem inverseACB_eq : associatorInverseZ 7 3 5 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 7 5) (LeftIndex 7 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms735.innerABC

theorem innerACB_eq : innerLeftZ 7 3 5 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms735.innerABC_eq

def assocBCA : Matrix (RightIndex 5 3 7) (LeftIndex 5 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBAC

theorem assocBCA_eq : associatorZ 5 3 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms357.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 5 3 7) (RightIndex 5 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms573.innerRightABC

theorem innerRightBAC_eq : innerRightZ 5 7 3 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms573.innerRightABC_eq

def assocCAB : Matrix (RightIndex 3 7 5) (LeftIndex 3 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocABC

theorem assocCAB_eq : associatorZ 3 7 5 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms375.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 7 5) (LeftIndex 7 5 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 5 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms753
