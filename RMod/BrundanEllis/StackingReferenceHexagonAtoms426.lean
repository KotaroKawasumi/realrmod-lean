import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21464554,
    decodeIntegerRow 16 3 1 21700426,
    decodeIntegerRow 16 3 1 21532108,
    decodeIntegerRow 16 3 1 21502948,
    decodeIntegerRow 16 3 1 21346132,
    decodeIntegerRow 16 3 1 21464068,
    decodeIntegerRow 16 3 1 21542314,
    decodeIntegerRow 16 3 1 21527734,
    decodeIntegerRow 16 3 1 20991946,
    decodeIntegerRow 16 3 1 19929046,
    decodeIntegerRow 16 3 1 16740388,
    decodeIntegerRow 16 3 1 7174452,
    decodeIntegerRow 16 3 1 19929028,
    decodeIntegerRow 16 3 1 22054828,
    decodeIntegerRow 16 3 1 7174454,
    decodeIntegerRow 16 3 1 26306326]

def assocABC : Matrix (RightIndex 4 2 6) (LeftIndex 4 2 6) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 2 6 r) []).getD (leftPosition 4 2 6 s) 0

theorem assocABC_eq : associatorZ 4 2 6 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 6 4) (RightIndex 4 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 2 6 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21759556,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21497116,
    decodeIntegerRow 16 3 1 21536482,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523342,
    decodeIntegerRow 16 3 1 21523396,
    decodeIntegerRow 16 3 1 23649124,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 40655236,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21523198,
    decodeIntegerRow 16 3 1 21523036]

def assocBAC : Matrix (RightIndex 2 4 6) (LeftIndex 2 4 6) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 4 6 r) []).getD (leftPosition 2 4 6 s) 0

theorem assocBAC_eq : associatorZ 2 4 6 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 4 6) (LeftIndex 4 2 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 4 2 6 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 4 6 2) (RightIndex 4 2 6) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 4 2 6 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523526,
    decodeIntegerRow 16 3 1 21523038,
    decodeIntegerRow 16 3 1 21524854,
    decodeIntegerRow 16 3 1 21520462,
    decodeIntegerRow 16 3 1 23636002,
    decodeIntegerRow 16 3 1 22612486,
    decodeIntegerRow 16 3 1 40537138,
    decodeIntegerRow 16 3 1 31325494,
    decodeIntegerRow 16 3 1 23662246,
    decodeIntegerRow 16 3 1 22559998,
    decodeIntegerRow 16 3 1 40773334,
    decodeIntegerRow 16 3 1 30853102,
    decodeIntegerRow 16 3 1 21523202,
    decodeIntegerRow 16 3 1 21523686,
    decodeIntegerRow 16 3 1 21521938,
    decodeIntegerRow 16 3 1 21526294]

def inverseACB : Matrix (LeftIndex 4 6 2) (RightIndex 4 6 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 6 2 r) []).getD (rightPosition 4 6 2 s) 0

theorem inverseACB_eq : associatorInverseZ 4 6 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 6 4 2) (LeftIndex 4 6 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 4 6 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523682,
    decodeIntegerRow 16 3 1 21523526,
    decodeIntegerRow 16 3 1 21526258,
    decodeIntegerRow 16 3 1 21524854,
    decodeIntegerRow 16 3 1 2509582,
    decodeIntegerRow 16 3 1 31325494,
    decodeIntegerRow 16 3 1 23636002,
    decodeIntegerRow 16 3 1 20434234,
    decodeIntegerRow 16 3 1 20486722,
    decodeIntegerRow 16 3 1 23662246,
    decodeIntegerRow 16 3 1 12193618,
    decodeIntegerRow 16 3 1 40773334,
    decodeIntegerRow 16 3 1 21524782,
    decodeIntegerRow 16 3 1 21526294,
    decodeIntegerRow 16 3 1 21523202,
    decodeIntegerRow 16 3 1 21523034]

def assocBCA : Matrix (RightIndex 2 6 4) (LeftIndex 2 6 4) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 6 4 r) []).getD (leftPosition 2 6 4 s) 0

theorem assocBCA_eq : associatorZ 2 6 4 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 6 4) (RightIndex 2 4 6) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 4 6 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21521902,
    decodeIntegerRow 16 3 1 21523036,
    decodeIntegerRow 16 3 1 21523522,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 40655236,
    decodeIntegerRow 16 3 1 20460478,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21523396,
    decodeIntegerRow 16 3 1 21523342,
    decodeIntegerRow 16 3 1 21523356,
    decodeIntegerRow 16 3 1 21523362,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21536482,
    decodeIntegerRow 16 3 1 21549604]

def assocCAB : Matrix (RightIndex 6 4 2) (LeftIndex 6 4 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 6 4 2 r) []).getD (leftPosition 6 4 2 s) 0

theorem assocCAB_eq : associatorZ 6 4 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21524089,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 20991919]

def outerLeftABC : Matrix (RightIndex 6 4 2) (LeftIndex 4 2 6) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 6 4 2 r) []).getD (leftPosition 4 2 6 s) 0

theorem outerLeftABC_eq : outerLeftZ 4 2 6 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms426
