import RMod.BrundanEllis.StackingReferenceHexagonAtoms317
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21516880,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21348400,
    decodeIntegerRow 16 3 1 20991918,
    decodeIntegerRow 16 3 1 19929040,
    decodeIntegerRow 16 3 1 16740400,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 22054800,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 16740382,
    decodeIntegerRow 16 3 1 35872240,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21344026]

def assocABC : Matrix (RightIndex 3 7 1) (LeftIndex 3 7 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 7 1 r) []).getD (leftPosition 3 7 1 s) 0

theorem assocABC_eq : associatorZ 3 7 1 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 7 1 3) (RightIndex 3 7 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 7 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 7 3 1) (LeftIndex 7 3 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocCAB

theorem assocBAC_eq : associatorZ 7 3 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocCAB_eq

def innerABC : Matrix (LeftIndex 7 3 1) (LeftIndex 3 7 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.innerACB

theorem innerABC_eq : innerLeftZ 3 7 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.innerACB_eq

def innerRightABC : Matrix (RightIndex 3 1 7) (RightIndex 3 7 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 7 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 22073728,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 16917460,
    decodeIntegerRow 16 3 1 35812976,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 19924672,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 35813460,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 21012304,
    decodeIntegerRow 16 3 1 19933420,
    decodeIntegerRow 16 3 1 16563160,
    decodeIntegerRow 16 3 1 7115648]

def inverseACB : Matrix (LeftIndex 3 1 7) (RightIndex 3 1 7) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 1 7 r) []).getD (rightPosition 3 1 7 s) 0

theorem inverseACB_eq : associatorInverseZ 3 1 7 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 3 7) (LeftIndex 3 1 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.innerABC

theorem innerACB_eq : innerLeftZ 3 1 7 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 20972992,
    decodeIntegerRow 16 3 1 23126440,
    decodeIntegerRow 16 3 1 26129260,
    decodeIntegerRow 16 3 1 7233744,
    decodeIntegerRow 16 3 1 19937776,
    decodeIntegerRow 16 3 1 22035820,
    decodeIntegerRow 16 3 1 7115160,
    decodeIntegerRow 16 3 1 26483392,
    decodeIntegerRow 16 3 1 23122048,
    decodeIntegerRow 16 3 1 22075240,
    decodeIntegerRow 16 3 1 7233260,
    decodeIntegerRow 16 3 1 16917616,
    decodeIntegerRow 16 3 1 22034416,
    decodeIntegerRow 16 3 1 23113300,
    decodeIntegerRow 16 3 1 26483560,
    decodeIntegerRow 16 3 1 35931072]

def assocBCA : Matrix (RightIndex 7 1 3) (LeftIndex 7 1 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 7 1 3 r) []).getD (leftPosition 7 1 3 s) 0

theorem assocBCA_eq : associatorZ 7 1 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 7 1 3) (RightIndex 7 3 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 7 3 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 1 3 7) (LeftIndex 1 3 7) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBAC

theorem assocCAB_eq : associatorZ 1 3 7 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms317.assocBAC_eq

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21522848,
    decodeIntegerRow 16 3 1 21521248,
    decodeIntegerRow 16 3 1 21521104,
    decodeIntegerRow 16 3 1 21522416,
    decodeIntegerRow 16 3 1 21521260,
    decodeIntegerRow 16 3 1 21522900,
    decodeIntegerRow 16 3 1 21524360,
    decodeIntegerRow 16 3 1 21525640,
    decodeIntegerRow 16 3 1 18164128,
    decodeIntegerRow 16 3 1 7666528,
    decodeIntegerRow 16 3 1 6721744,
    decodeIntegerRow 16 3 1 15329776,
    decodeIntegerRow 16 3 1 7745260,
    decodeIntegerRow 16 3 1 18505300,
    decodeIntegerRow 16 3 1 28084360,
    decodeIntegerRow 16 3 1 36482440]

def outerLeftABC : Matrix (RightIndex 1 3 7) (LeftIndex 3 7 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 3 7 r) []).getD (leftPosition 3 7 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 3 7 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms371
