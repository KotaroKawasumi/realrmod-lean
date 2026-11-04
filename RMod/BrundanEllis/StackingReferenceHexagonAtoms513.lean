import RMod.BrundanEllis.StackingReferenceHexagonAtoms315
import RMod.BrundanEllis.StackingReferenceHexagonAtoms351
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms513
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 1 3) (LeftIndex 5 1 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.assocBCA

theorem assocABC_eq : associatorZ 5 1 3 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.assocBCA_eq

def outerABC : Matrix (LeftIndex 1 3 5) (RightIndex 5 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 1 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 1 5 3) (LeftIndex 1 5 3) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBCA

theorem assocBAC_eq : associatorZ 1 5 3 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBCA_eq

def innerABC : Matrix (LeftIndex 1 5 3) (LeftIndex 5 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 1 3 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 5 3 1) (RightIndex 5 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 1 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
    decodeIntegerRow 16 3 1 19988818,
    decodeIntegerRow 16 3 1 26325778,
    decodeIntegerRow 16 3 1 35865814,
    decodeIntegerRow 16 3 1 21879842,
    decodeIntegerRow 16 3 1 23176006,
    decodeIntegerRow 16 3 1 26286394,
    decodeIntegerRow 16 3 1 35878882,
    decodeIntegerRow 16 3 1 7167946,
    decodeIntegerRow 16 3 1 26286898,
    decodeIntegerRow 16 3 1 23177458,
    decodeIntegerRow 16 3 1 21171254,
    decodeIntegerRow 16 3 1 7181122,
    decodeIntegerRow 16 3 1 26326246,
    decodeIntegerRow 16 3 1 19987354,
    decodeIntegerRow 16 3 1 22229762]

def inverseACB : Matrix (LeftIndex 5 3 1) (RightIndex 5 3 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 3 1 r) []).getD (rightPosition 5 3 1 s) 0

theorem inverseACB_eq : associatorInverseZ 5 3 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 3 5 1) (LeftIndex 5 3 1) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 5 3 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 3 5) (LeftIndex 1 3 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBAC

theorem assocBCA_eq : associatorZ 1 3 5 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms315.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 1 3 5) (RightIndex 1 5 3) ℤ :=
  (show Matrix (Fin 8 × Fin 1 × Fin 2) (Fin 8 × Fin 1 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 5 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 3 5 1) (LeftIndex 3 5 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.assocABC

theorem assocCAB_eq : associatorZ 3 5 1 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms351.assocABC_eq

def outerLeftABC : Matrix (RightIndex 3 5 1) (LeftIndex 5 1 3) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 1 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms513
