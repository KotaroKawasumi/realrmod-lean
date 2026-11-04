import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 6471448,
    decodeIntegerRow 16 3 1 15104408,
    decodeIntegerRow 16 3 1 7890076,
    decodeIntegerRow 16 3 1 18415524,
    decodeIntegerRow 16 3 1 24635352,
    decodeIntegerRow 16 3 1 35157592,
    decodeIntegerRow 16 3 1 27937724,
    decodeIntegerRow 16 3 1 36573316,
    decodeIntegerRow 16 3 1 15183192,
    decodeIntegerRow 16 3 1 6812632,
    decodeIntegerRow 16 3 1 24788604,
    decodeIntegerRow 16 3 1 35524036,
    decodeIntegerRow 16 3 1 35525032,
    decodeIntegerRow 16 3 1 24792872,
    decodeIntegerRow 16 3 1 6814564,
    decodeIntegerRow 16 3 1 15187676]

def assocABC : Matrix (RightIndex 3 6 6) (LeftIndex 3 6 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 6 6 r) []).getD (leftPosition 3 6 6 s) 0

theorem assocABC_eq : associatorZ 3 6 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 6 6 3) (RightIndex 3 6 6) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 6 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 21169318,
    decodeIntegerRow 16 3 1 35879554,
    decodeIntegerRow 16 3 1 26328198,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7168618,
    decodeIntegerRow 16 3 1 21168814,
    decodeIntegerRow 16 3 1 19987978,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 23176786,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 35866438,
    decodeIntegerRow 16 3 1 26288834,
    decodeIntegerRow 16 3 1 19870042,
    decodeIntegerRow 16 3 1 20815006]

def assocBAC : Matrix (RightIndex 6 3 6) (LeftIndex 6 3 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 6 3 6 r) []).getD (leftPosition 6 3 6 s) 0

theorem assocBAC_eq : associatorZ 6 3 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 6 3 6) (LeftIndex 3 6 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 6 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523117,
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

def innerRightABC : Matrix (RightIndex 3 6 6) (RightIndex 3 6 6) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 3 6 6 r) []).getD (rightPosition 3 6 6 s) 0

theorem innerRightABC_eq : innerRightZ 3 6 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 37401604,
    decodeIntegerRow 16 3 1 26642876,
    decodeIntegerRow 16 3 1 17111928,
    decodeIntegerRow 16 3 1 8715448,
    decodeIntegerRow 16 3 1 34329592,
    decodeIntegerRow 16 3 1 25929912,
    decodeIntegerRow 16 3 1 26639004,
    decodeIntegerRow 16 3 1 37400356,
    decodeIntegerRow 16 3 1 17426876,
    decodeIntegerRow 16 3 1 8820484,
    decodeIntegerRow 16 3 1 37532872,
    decodeIntegerRow 16 3 1 27036552,
    decodeIntegerRow 16 3 1 16014072,
    decodeIntegerRow 16 3 1 5515192,
    decodeIntegerRow 16 3 1 8822044,
    decodeIntegerRow 16 3 1 17431716]

def inverseACB : Matrix (LeftIndex 3 6 6) (RightIndex 3 6 6) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 6 6 r) []).getD (rightPosition 3 6 6 s) 0

theorem inverseACB_eq : associatorInverseZ 3 6 6 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 3 6) (LeftIndex 3 6 6) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 3 6 6 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 5515360,
    decodeIntegerRow 16 3 1 16014560,
    decodeIntegerRow 16 3 1 25619360,
    decodeIntegerRow 16 3 1 34226080,
    decodeIntegerRow 16 3 1 8821888,
    decodeIntegerRow 16 3 1 17431232,
    decodeIntegerRow 16 3 1 16009680,
    decodeIntegerRow 16 3 1 5513680,
    decodeIntegerRow 16 3 1 17112416,
    decodeIntegerRow 16 3 1 8715616,
    decodeIntegerRow 16 3 1 37400200,
    decodeIntegerRow 16 3 1 26638520,
    decodeIntegerRow 16 3 1 16403360,
    decodeIntegerRow 16 3 1 5644960,
    decodeIntegerRow 16 3 1 8716960,
    decodeIntegerRow 16 3 1 17116320]

def assocBCA : Matrix (RightIndex 6 6 3) (LeftIndex 6 6 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 6 6 3 r) []).getD (leftPosition 6 6 3 s) 0

theorem assocBCA_eq : associatorZ 6 6 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 6 6 3) (RightIndex 6 3 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 6 3 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 6 3 6) (LeftIndex 6 3 6) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 6 3 6 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 6 3 6) (LeftIndex 3 6 6) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 6 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms366
