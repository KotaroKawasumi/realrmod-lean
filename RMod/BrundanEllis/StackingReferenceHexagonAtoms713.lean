import RMod.BrundanEllis.StackingReferenceHexagonAtoms317
import RMod.BrundanEllis.StackingReferenceHexagonAtoms371
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms713
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 1 3) (LeftIndex 7 1 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.assocBCA

theorem assocABC_eq : associatorZ 7 1 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.assocBCA_eq

def outerABC : Matrix (LeftIndex 1 3 7) (RightIndex 7 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 1 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 1 7 3) (LeftIndex 1 7 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBCA

theorem assocBAC_eq : associatorZ 1 7 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBCA_eq

def innerABC : Matrix (LeftIndex 1 7 3) (LeftIndex 7 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 1 3 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 3 1) (RightIndex 7 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 7 1 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18153100,
    decodeIntegerRow 16 3 1 7626704,
    decodeIntegerRow 16 3 1 6604592,
    decodeIntegerRow 16 3 1 14973220,
    decodeIntegerRow 16 3 1 6681380,
    decodeIntegerRow 16 3 1 15318928,
    decodeIntegerRow 16 3 1 18516304,
    decodeIntegerRow 16 3 1 7785140,
    decodeIntegerRow 16 3 1 35262608,
    decodeIntegerRow 16 3 1 18520540,
    decodeIntegerRow 16 3 1 27732340,
    decodeIntegerRow 16 3 1 6683376,
    decodeIntegerRow 16 3 1 14977744,
    decodeIntegerRow 16 3 1 36444020,
    decodeIntegerRow 16 3 1 7627620,
    decodeIntegerRow 16 3 1 24897808]

def inverseACB : Matrix (LeftIndex 7 3 1) (RightIndex 7 3 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 3 1 r) []).getD (rightPosition 7 3 1 s) 0

theorem inverseACB_eq : associatorInverseZ 7 3 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 7 1) (LeftIndex 7 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 7 3 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 3 7) (LeftIndex 1 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBAC

theorem assocBCA_eq : associatorZ 1 3 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 1 3 7) (RightIndex 1 7 3) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 7 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 3 7 1) (LeftIndex 3 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.assocABC

theorem assocCAB_eq : associatorZ 3 7 1 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 7 1) (LeftIndex 7 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 1 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms713
