import RMod.BrundanEllis.StackingReferenceHexagonAtoms517
import RMod.BrundanEllis.StackingReferenceHexagonAtoms571
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms715
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 1 5) (LeftIndex 7 1 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.assocBCA

theorem assocABC_eq : associatorZ 7 1 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522848,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21521260,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21521248,
    decodeIntegerRow 16 3 1 21524304,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 6721744,
    decodeIntegerRow 16 3 1 7745260,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 36482440]

def outerABC : Matrix (LeftIndex 1 5 7) (RightIndex 7 1 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 1 5 7 r) []).getD (rightPosition 7 1 5 s) 0

theorem outerABC_eq : outerRightZ 7 1 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 1 7 5) (LeftIndex 1 7 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBCA

theorem assocBAC_eq : associatorZ 1 7 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBCA_eq

def innerABC : Matrix (LeftIndex 1 7 5) (LeftIndex 7 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 1 5 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 5 1) (RightIndex 7 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 7 1 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18503044,
    decodeIntegerRow 16 3 1 6563768,
    decodeIntegerRow 16 3 1 7667528,
    decodeIntegerRow 16 3 1 27714844,
    decodeIntegerRow 16 3 1 35302404,
    decodeIntegerRow 16 3 1 14960248,
    decodeIntegerRow 16 3 1 18166408,
    decodeIntegerRow 16 3 1 6722204,
    decodeIntegerRow 16 3 1 6564792,
    decodeIntegerRow 16 3 1 18507556,
    decodeIntegerRow 16 3 1 27719044,
    decodeIntegerRow 16 3 1 7665528,
    decodeIntegerRow 16 3 1 14964472,
    decodeIntegerRow 16 3 1 35300516,
    decodeIntegerRow 16 3 1 6721284,
    decodeIntegerRow 16 3 1 18161848]

def inverseACB : Matrix (LeftIndex 7 5 1) (RightIndex 7 5 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 5 1 r) []).getD (rightPosition 7 5 1 s) 0

theorem inverseACB_eq : associatorInverseZ 7 5 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 7 1) (LeftIndex 7 5 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 7 5 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 1 5 7) (LeftIndex 1 5 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBAC

theorem assocBCA_eq : associatorZ 1 5 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms517.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 1 5 7) (RightIndex 1 7 5) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 7 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 7 1) (LeftIndex 5 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.assocABC

theorem assocCAB_eq : associatorZ 5 7 1 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms571.assocABC_eq

def outerLeftABC : Matrix (RightIndex 5 7 1) (LeftIndex 7 1 5) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 1 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms715
