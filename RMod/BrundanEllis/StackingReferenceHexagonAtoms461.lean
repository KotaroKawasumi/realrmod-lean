import RMod.BrundanEllis.StackingReferenceHexagonAtoms416
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461
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

def assocABC : Matrix (RightIndex 4 6 1) (LeftIndex 4 6 1) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 6 1 r) []).getD (leftPosition 4 6 1 s) 0

theorem assocABC_eq : associatorZ 4 6 1 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 1 4) (RightIndex 4 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 6 1 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 4 1) (LeftIndex 6 4 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocCAB

theorem assocBAC_eq : associatorZ 6 4 1 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 4 1) (LeftIndex 4 6 1) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.innerACB

theorem innerABC_eq : innerLeftZ 4 6 1 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.innerACB_eq

def innerRightABC : Matrix (RightIndex 4 1 6) (RightIndex 4 6 1) ℤ :=
  (show Matrix (Fin 2 × Fin 1 × Fin 8) (Fin 2 × Fin 1 × Fin 8) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 6 1 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21483022,
    decodeIntegerRow 16 3 1 21691678,
    decodeIntegerRow 16 3 1 21709174,
    decodeIntegerRow 16 3 1 21445114,
    decodeIntegerRow 16 3 1 18334726,
    decodeIntegerRow 16 3 1 35340854,
    decodeIntegerRow 16 3 1 36403682,
    decodeIntegerRow 16 3 1 15146062,
    decodeIntegerRow 16 3 1 21704962,
    decodeIntegerRow 16 3 1 21602578,
    decodeIntegerRow 16 3 1 21561754,
    decodeIntegerRow 16 3 1 21696214,
    decodeIntegerRow 16 3 1 36403734,
    decodeIntegerRow 16 3 1 27900646,
    decodeIntegerRow 16 3 1 24712018,
    decodeIntegerRow 16 3 1 35340798]

def inverseACB : Matrix (LeftIndex 4 1 6) (RightIndex 4 1 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 1 6 r) []).getD (rightPosition 4 1 6 s) 0

theorem inverseACB_eq : associatorInverseZ 4 1 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 1 4 6) (LeftIndex 4 1 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.innerABC

theorem innerACB_eq : innerLeftZ 4 1 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21563698,
    decodeIntegerRow 16 3 1 21355042,
    decodeIntegerRow 16 3 1 21337546,
    decodeIntegerRow 16 3 1 21601606,
    decodeIntegerRow 16 3 1 24711994,
    decodeIntegerRow 16 3 1 7705866,
    decodeIntegerRow 16 3 1 6643038,
    decodeIntegerRow 16 3 1 27900658,
    decodeIntegerRow 16 3 1 21341758,
    decodeIntegerRow 16 3 1 21444142,
    decodeIntegerRow 16 3 1 21484966,
    decodeIntegerRow 16 3 1 21350506,
    decodeIntegerRow 16 3 1 6642986,
    decodeIntegerRow 16 3 1 15146074,
    decodeIntegerRow 16 3 1 18334702,
    decodeIntegerRow 16 3 1 7705922]

def assocBCA : Matrix (RightIndex 6 1 4) (LeftIndex 6 1 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 1 4 r) []).getD (leftPosition 6 1 4 s) 0

theorem assocBCA_eq : associatorZ 6 1 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 1 4) (RightIndex 6 4 1) ℤ :=
  (show Matrix (Fin 1 × Fin 2 × Fin 8) (Fin 1 × Fin 2 × Fin 8) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 4 1 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 1 4 6) (LeftIndex 1 4 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBAC

theorem assocCAB_eq : associatorZ 1 4 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms416.assocBAC_eq

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

def outerLeftABC : Matrix (RightIndex 1 4 6) (LeftIndex 4 6 1) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 1 4 6 r) []).getD (leftPosition 4 6 1 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 6 1 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms461
