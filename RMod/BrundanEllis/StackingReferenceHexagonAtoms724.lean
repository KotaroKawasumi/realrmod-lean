import RMod.BrundanEllis.StackingReferenceHexagonAtoms427
import RMod.BrundanEllis.StackingReferenceHexagonAtoms472
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms724
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 2 4) (LeftIndex 7 2 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.assocBCA

theorem assocABC_eq : associatorZ 7 2 4 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.assocBCA_eq

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

def outerABC : Matrix (LeftIndex 2 4 7) (RightIndex 7 2 4) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 4 7 r) []).getD (rightPosition 7 2 4 s) 0

theorem outerABC_eq : outerRightZ 7 2 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 2 7 4) (LeftIndex 2 7 4) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBCA

theorem assocBAC_eq : associatorZ 2 7 4 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBCA_eq

def innerABC : Matrix (LeftIndex 2 7 4) (LeftIndex 7 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerABC_eq : innerLeftZ 7 2 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 4 2) (RightIndex 7 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 7 2 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35380192,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 6564280,
    decodeIntegerRow 16 3 1 24882592,
    decodeIntegerRow 16 3 1 6721744,
    decodeIntegerRow 16 3 1 7745260,
    decodeIntegerRow 16 3 1 14962360,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21522848,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21521260,
    decodeIntegerRow 16 3 1 21524304,
    decodeIntegerRow 16 3 1 21521248,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 21523820]

def inverseACB : Matrix (LeftIndex 7 4 2) (RightIndex 7 4 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 4 2 r) []).getD (rightPosition 7 4 2 s) 0

theorem inverseACB_eq : associatorInverseZ 7 4 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 7 2) (LeftIndex 7 4 2) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerACB_eq : innerLeftZ 7 4 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBCA : Matrix (RightIndex 2 4 7) (LeftIndex 2 4 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBAC

theorem assocBCA_eq : associatorZ 2 4 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms427.assocBAC_eq

def innerRightBAC : Matrix (RightIndex 2 4 7) (RightIndex 2 7 4) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 7 4 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 4 7 2) (LeftIndex 4 7 2) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.assocABC

theorem assocCAB_eq : associatorZ 4 7 2 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms472.assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 7 2) (LeftIndex 7 2 4) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 2 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms724
