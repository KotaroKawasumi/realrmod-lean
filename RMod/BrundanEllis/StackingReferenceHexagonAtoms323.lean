import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms323
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 21524818,
    decodeIntegerRow 16 3 1 21549604,
    decodeIntegerRow 16 3 1 21536482,
    decodeIntegerRow 16 3 1 11957422,
    decodeIntegerRow 16 3 1 40655236,
    decodeIntegerRow 16 3 1 21523358,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21523378,
    decodeIntegerRow 16 3 1 21523324,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21523036,
    decodeIntegerRow 16 3 1 21523198]

def assocABC : Matrix (RightIndex 3 2 3) (LeftIndex 3 2 3) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 3 r) []).getD (leftPosition 3 2 3 s) 0

theorem assocABC_eq : associatorZ 3 2 3 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def outerABC : Matrix (LeftIndex 2 3 3) (RightIndex 3 2 3) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 3 3 r) []).getD (rightPosition 3 2 3 s) 0

theorem outerABC_eq : outerRightZ 3 2 3 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523328,
    decodeIntegerRow 16 3 1 21523344,
    decodeIntegerRow 16 3 1 21785800,
    decodeIntegerRow 16 3 1 21392140,
    decodeIntegerRow 16 3 1 21523320,
    decodeIntegerRow 16 3 1 21523340,
    decodeIntegerRow 16 3 1 21313408,
    decodeIntegerRow 16 3 1 21628336,
    decodeIntegerRow 16 3 1 21526600,
    decodeIntegerRow 16 3 1 21524980,
    decodeIntegerRow 16 3 1 4517248,
    decodeIntegerRow 16 3 1 30026416,
    decodeIntegerRow 16 3 1 21520768,
    decodeIntegerRow 16 3 1 21522064,
    decodeIntegerRow 16 3 1 265720,
    decodeIntegerRow 16 3 1 32152180]

def assocBAC : Matrix (RightIndex 2 3 3) (LeftIndex 2 3 3) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 3 r) []).getD (leftPosition 2 3 3 s) 0

theorem assocBAC_eq : associatorZ 2 3 3 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 3 3) (LeftIndex 3 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 8 × Fin 1) (Fin 2 × Fin 8 × Fin 1) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 2 3 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 3 2) (RightIndex 3 2 3) ℤ :=
  (show Matrix (Fin 2 × Fin 8 × Fin 1) (Fin 2 × Fin 8 × Fin 1) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 2 3 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21545230,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 23117656,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21517528,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 19929010,
    decodeIntegerRow 16 3 1 16740392,
    decodeIntegerRow 16 3 1 7174456,
    decodeIntegerRow 16 3 1 21345970,
    decodeIntegerRow 16 3 1 21464230,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 21700264,
    decodeIntegerRow 16 3 1 21582328]

def inverseACB : Matrix (LeftIndex 3 3 2) (RightIndex 3 3 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 3 2 r) []).getD (rightPosition 3 3 2 s) 0

theorem inverseACB_eq : associatorInverseZ 3 3 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23621404,
    decodeIntegerRow 16 3 1 22570168,
    decodeIntegerRow 16 3 1 40418876,
    decodeIntegerRow 16 3 1 30970872,
    decodeIntegerRow 16 3 1 19422364,
    decodeIntegerRow 16 3 1 20470648,
    decodeIntegerRow 16 3 1 2627516,
    decodeIntegerRow 16 3 1 12075192,
    decodeIntegerRow 16 3 1 40891272,
    decodeIntegerRow 16 3 1 11839644,
    decodeIntegerRow 16 3 1 23673928,
    decodeIntegerRow 16 3 1 20450236,
    decodeIntegerRow 16 3 1 40891592,
    decodeIntegerRow 16 3 1 11839004,
    decodeIntegerRow 16 3 1 23676808,
    decodeIntegerRow 16 3 1 20444476]

def innerACB : Matrix (LeftIndex 3 3 2) (LeftIndex 3 3 2) ℤ :=
  fun r s => ((innerACBRows).getD (leftPosition 3 3 2 r) []).getD (leftPosition 3 3 2 s) 0

theorem innerACB_eq : innerLeftZ 3 3 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523328,
    decodeIntegerRow 16 3 1 21523344,
    decodeIntegerRow 16 3 1 21785800,
    decodeIntegerRow 16 3 1 21392140,
    decodeIntegerRow 16 3 1 21523320,
    decodeIntegerRow 16 3 1 21523340,
    decodeIntegerRow 16 3 1 21313408,
    decodeIntegerRow 16 3 1 21628336,
    decodeIntegerRow 16 3 1 21526600,
    decodeIntegerRow 16 3 1 21524980,
    decodeIntegerRow 16 3 1 4517248,
    decodeIntegerRow 16 3 1 30026416,
    decodeIntegerRow 16 3 1 21520768,
    decodeIntegerRow 16 3 1 21522064,
    decodeIntegerRow 16 3 1 265720,
    decodeIntegerRow 16 3 1 32152180]

def assocBCA : Matrix (RightIndex 2 3 3) (LeftIndex 2 3 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 3 3 r) []).getD (leftPosition 2 3 3 s) 0

theorem assocBCA_eq : associatorZ 2 3 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23621404,
    decodeIntegerRow 16 3 1 22570168,
    decodeIntegerRow 16 3 1 40418876,
    decodeIntegerRow 16 3 1 30970872,
    decodeIntegerRow 16 3 1 19422364,
    decodeIntegerRow 16 3 1 20470648,
    decodeIntegerRow 16 3 1 2627516,
    decodeIntegerRow 16 3 1 12075192,
    decodeIntegerRow 16 3 1 40891272,
    decodeIntegerRow 16 3 1 11839644,
    decodeIntegerRow 16 3 1 23673928,
    decodeIntegerRow 16 3 1 20450236,
    decodeIntegerRow 16 3 1 40891592,
    decodeIntegerRow 16 3 1 11839004,
    decodeIntegerRow 16 3 1 23676808,
    decodeIntegerRow 16 3 1 20444476]

def innerRightBAC : Matrix (RightIndex 2 3 3) (RightIndex 2 3 3) ℤ :=
  fun r s => ((innerRightBACRows).getD (rightPosition 2 3 3 r) []).getD (rightPosition 2 3 3 s) 0

theorem innerRightBAC_eq : innerRightZ 2 3 3 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 20998480,
    decodeIntegerRow 16 3 1 19948720,
    decodeIntegerRow 16 3 1 21524098,
    decodeIntegerRow 16 3 1 21521146,
    decodeIntegerRow 16 3 1 6997306,
    decodeIntegerRow 16 3 1 16681342,
    decodeIntegerRow 16 3 1 21523600,
    decodeIntegerRow 16 3 1 21523280,
    decodeIntegerRow 16 3 1 21523114,
    decodeIntegerRow 16 3 1 21523442,
    decodeIntegerRow 16 3 1 35695120,
    decodeIntegerRow 16 3 1 26247280,
    decodeIntegerRow 16 3 1 21524080,
    decodeIntegerRow 16 3 1 21521200,
    decodeIntegerRow 16 3 1 20985358,
    decodeIntegerRow 16 3 1 19909354]

def assocCAB : Matrix (RightIndex 3 3 2) (LeftIndex 3 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 3 3 2 r) []).getD (leftPosition 3 3 2 s) 0

theorem assocCAB_eq : associatorZ 3 3 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerLeftABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523357,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21523333,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 21582409,
    decodeIntegerRow 16 3 1 21700507,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267]

def outerLeftABC : Matrix (RightIndex 3 3 2) (LeftIndex 3 2 3) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 3 3 2 r) []).getD (leftPosition 3 2 3 s) 0

theorem outerLeftABC_eq : outerLeftZ 3 2 3 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms323
