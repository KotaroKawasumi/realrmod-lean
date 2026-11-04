import RMod.BrundanEllis.StackingReferenceHexagonAtoms667
import RMod.BrundanEllis.StackingReferenceHexagonAtoms676
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms766
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 7 6 6) (LeftIndex 7 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocCAB

theorem assocABC_eq : associatorZ 7 6 6 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocCAB_eq

def outerABC : Matrix (LeftIndex 6 6 7) (RightIndex 7 6 6) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 7 6 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 7 6) (LeftIndex 6 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocBCA

theorem assocBAC_eq : associatorZ 6 7 6 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocBCA_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21525472,
    decodeIntegerRow 16 3 1 21523872,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21523820,
    decodeIntegerRow 16 3 1 21525460,
    decodeIntegerRow 16 3 1 24541420,
    decodeIntegerRow 16 3 1 35301460,
    decodeIntegerRow 16 3 1 36482440,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 27716944,
    decodeIntegerRow 16 3 1 36324976]

def innerABC : Matrix (LeftIndex 6 7 6) (LeftIndex 7 6 6) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 6 7 6 r) []).getD (leftPosition 7 6 6 s) 0

theorem innerABC_eq : innerLeftZ 7 6 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 7 6 6) (RightIndex 7 6 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms676.innerRightBAC

theorem innerRightABC_eq : innerRightZ 7 6 6 = innerRightABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms676.innerRightBAC_eq

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7154986,
    decodeIntegerRow 16 3 1 26312962,
    decodeIntegerRow 16 3 1 19749706,
    decodeIntegerRow 16 3 1 22113122,
    decodeIntegerRow 16 3 1 20103994,
    decodeIntegerRow 16 3 1 21995022,
    decodeIntegerRow 16 3 1 7194406,
    decodeIntegerRow 16 3 1 26299858,
    decodeIntegerRow 16 3 1 16747042,
    decodeIntegerRow 16 3 1 7193866,
    decodeIntegerRow 16 3 1 21050238,
    decodeIntegerRow 16 3 1 20108374,
    decodeIntegerRow 16 3 1 22114578,
    decodeIntegerRow 16 3 1 23292646,
    decodeIntegerRow 16 3 1 26312818,
    decodeIntegerRow 16 3 1 35892166]

def inverseACB : Matrix (LeftIndex 7 6 6) (RightIndex 7 6 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 7 6 6 r) []).getD (rightPosition 7 6 6 s) 0

theorem inverseACB_eq : associatorInverseZ 7 6 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 7 6) (LeftIndex 7 6 6) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 7 6 6 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 6 6 7) (LeftIndex 6 6 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocABC

theorem assocBCA_eq : associatorZ 6 6 7 = assocBCA := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms667.assocABC_eq

def innerRightBAC : Matrix (RightIndex 6 6 7) (RightIndex 6 7 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms676.innerRightABC

theorem innerRightBAC_eq : innerRightZ 6 7 6 = innerRightBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms676.innerRightABC_eq

def assocCAB : Matrix (RightIndex 6 7 6) (LeftIndex 6 7 6) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 6 7 6 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 6 7 6) (LeftIndex 7 6 6) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 7 6 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms766
