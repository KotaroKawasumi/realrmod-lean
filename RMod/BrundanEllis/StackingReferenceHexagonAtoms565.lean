import RMod.BrundanEllis.StackingReferenceHexagonAtoms556
import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms565
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

def assocABC : Matrix (RightIndex 5 6 5) (LeftIndex 5 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocBCA

theorem assocABC_eq : associatorZ 5 6 5 = assocABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocBCA_eq

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
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

def outerABC : Matrix (LeftIndex 6 5 5) (RightIndex 5 6 5) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 6 5 5 r) []).getD (rightPosition 5 6 5 s) 0

theorem outerABC_eq : outerRightZ 5 6 5 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 6 5 5) (LeftIndex 6 5 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocCAB

theorem assocBAC_eq : associatorZ 6 5 5 = assocBAC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocCAB_eq

def innerABC : Matrix (LeftIndex 6 5 5) (LeftIndex 5 6 5) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.innerACB

theorem innerABC_eq : innerLeftZ 5 6 5 = innerABC := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.innerACB_eq

def innerRightABC : Matrix (RightIndex 5 5 6) (RightIndex 5 6 5) ℤ :=
  (show Matrix (Fin 2 × Fin 8 × Fin 1) (Fin 2 × Fin 8 × Fin 1) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 5 6 5 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21666568,
    decodeIntegerRow 16 3 1 21743356,
    decodeIntegerRow 16 3 1 41718152,
    decodeIntegerRow 16 3 1 28963556,
    decodeIntegerRow 16 3 1 21749512,
    decodeIntegerRow 16 3 1 21668836,
    decodeIntegerRow 16 3 1 28963512,
    decodeIntegerRow 16 3 1 41718084,
    decodeIntegerRow 16 3 1 33215048,
    decodeIntegerRow 16 3 1 39592316,
    decodeIntegerRow 16 3 1 21775432,
    decodeIntegerRow 16 3 1 21616996,
    decodeIntegerRow 16 3 1 39592392,
    decodeIntegerRow 16 3 1 33215076,
    decodeIntegerRow 16 3 1 21613432,
    decodeIntegerRow 16 3 1 21769924]

def inverseACB : Matrix (LeftIndex 5 5 6) (RightIndex 5 5 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 5 6 r) []).getD (rightPosition 5 5 6 s) 0

theorem inverseACB_eq : associatorInverseZ 5 5 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 5 5 6) (LeftIndex 5 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.innerABC

theorem innerACB_eq : innerLeftZ 5 5 6 = innerACB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.innerABC_eq

def assocBCA : Matrix (RightIndex 6 5 5) (LeftIndex 6 5 5) ℤ := assocBAC

theorem assocBCA_eq : associatorZ 6 5 5 = assocBCA := assocBAC_eq

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20431336,
    decodeIntegerRow 16 3 1 23634508,
    decodeIntegerRow 16 3 1 40773176,
    decodeIntegerRow 16 3 1 30853428,
    decodeIntegerRow 16 3 1 19409224,
    decodeIntegerRow 16 3 1 20437132,
    decodeIntegerRow 16 3 1 30852776,
    decodeIntegerRow 16 3 1 2273228,
    decodeIntegerRow 16 3 1 31325816,
    decodeIntegerRow 16 3 1 2509748,
    decodeIntegerRow 16 3 1 23660824,
    decodeIntegerRow 16 3 1 22562932,
    decodeIntegerRow 16 3 1 2509416,
    decodeIntegerRow 16 3 1 11721548,
    decodeIntegerRow 16 3 1 20489656,
    decodeIntegerRow 16 3 1 23663668]

def innerRightBAC : Matrix (RightIndex 6 5 5) (RightIndex 6 5 5) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 6 5 5 r) []).getD (rightPosition 6 5 5 s) 0

theorem innerRightBAC_eq : innerRightZ 6 5 5 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 5 5 6) (LeftIndex 5 5 6) ℤ := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocABC

theorem assocCAB_eq : associatorZ 5 5 6 = assocCAB := RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms556.assocABC_eq

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

def outerLeftABC : Matrix (RightIndex 5 5 6) (LeftIndex 5 6 5) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 5 5 6 r) []).getD (leftPosition 5 6 5 s) 0

theorem outerLeftABC_eq : outerLeftZ 5 6 5 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms565
