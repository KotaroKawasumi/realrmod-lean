import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 18334742,
    decodeIntegerRow 16 3 1 35340838,
    decodeIntegerRow 16 3 1 36403714,
    decodeIntegerRow 16 3 1 15146094,
    decodeIntegerRow 16 3 1 21446734,
    decodeIntegerRow 16 3 1 21707554,
    decodeIntegerRow 16 3 1 21351802,
    decodeIntegerRow 16 3 1 21560458,
    decodeIntegerRow 16 3 1 21604198,
    decodeIntegerRow 16 3 1 21340138,
    decodeIntegerRow 16 3 1 21692974,
    decodeIntegerRow 16 3 1 21481726,
    decodeIntegerRow 16 3 1 24712034,
    decodeIntegerRow 16 3 1 7705906,
    decodeIntegerRow 16 3 1 6643018,
    decodeIntegerRow 16 3 1 27900678]

def assocABC : Matrix (RightIndex 3 2 7) (LeftIndex 3 2 7) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 7 r) []).getD (leftPosition 3 2 7 s) 0

theorem assocABC_eq : associatorZ 3 2 7 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

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

def outerABC : Matrix (LeftIndex 2 7 3) (RightIndex 3 2 7) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 2 7 3 r) []).getD (rightPosition 3 2 7 s) 0

theorem outerABC_eq : outerRightZ 3 2 7 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523198,
    decodeIntegerRow 16 3 1 21523684,
    decodeIntegerRow 16 3 1 21521902,
    decodeIntegerRow 16 3 1 21526276,
    decodeIntegerRow 16 3 1 22586242,
    decodeIntegerRow 16 3 1 19397596,
    decodeIntegerRow 16 3 1 31089298,
    decodeIntegerRow 16 3 1 2391484,
    decodeIntegerRow 16 3 1 21523342,
    decodeIntegerRow 16 3 1 21523324,
    decodeIntegerRow 16 3 1 21523362,
    decodeIntegerRow 16 3 1 21523364,
    decodeIntegerRow 16 3 1 21405262,
    decodeIntegerRow 16 3 1 21287164,
    decodeIntegerRow 16 3 1 21536482,
    decodeIntegerRow 16 3 1 21549604]

def assocBAC : Matrix (RightIndex 2 3 7) (LeftIndex 2 3 7) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 7 r) []).getD (leftPosition 2 3 7 s) 0

theorem assocBAC_eq : associatorZ 2 3 7 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 3 7) (LeftIndex 3 2 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 2 7 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightABC : Matrix (RightIndex 3 7 2) (RightIndex 3 2 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightABC_eq : innerRightZ 3 2 7 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21257680,
    decodeIntegerRow 16 3 1 21629632,
    decodeIntegerRow 16 3 1 21310816,
    decodeIntegerRow 16 3 1 21390520,
    decodeIntegerRow 16 3 1 265760,
    decodeIntegerRow 16 3 1 30026400,
    decodeIntegerRow 16 3 1 4517280,
    decodeIntegerRow 16 3 1 10894560,
    decodeIntegerRow 16 3 1 265680,
    decodeIntegerRow 16 3 1 30026432,
    decodeIntegerRow 16 3 1 4517216,
    decodeIntegerRow 16 3 1 10894520,
    decodeIntegerRow 16 3 1 21782560,
    decodeIntegerRow 16 3 1 21419680,
    decodeIntegerRow 16 3 1 21730720,
    decodeIntegerRow 16 3 1 21652960]

def inverseACB : Matrix (LeftIndex 3 7 2) (RightIndex 3 7 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 7 2 r) []).getD (rightPosition 3 7 2 s) 0

theorem inverseACB_eq : associatorInverseZ 3 7 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 7 3 2) (LeftIndex 3 7 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 7 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 21419680,
    decodeIntegerRow 16 3 1 21264160,
    decodeIntegerRow 16 3 1 21652960,
    decodeIntegerRow 16 3 1 21316000,
    decodeIntegerRow 16 3 1 38529504,
    decodeIntegerRow 16 3 1 10894520,
    decodeIntegerRow 16 3 1 265680,
    decodeIntegerRow 16 3 1 13020288,
    decodeIntegerRow 16 3 1 13020320,
    decodeIntegerRow 16 3 1 265760,
    decodeIntegerRow 16 3 1 32152160,
    decodeIntegerRow 16 3 1 4517280,
    decodeIntegerRow 16 3 1 21310816,
    decodeIntegerRow 16 3 1 21656200,
    decodeIntegerRow 16 3 1 21789040,
    decodeIntegerRow 16 3 1 21629632]

def assocBCA : Matrix (RightIndex 2 7 3) (LeftIndex 2 7 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 7 3 r) []).getD (leftPosition 2 7 3 s) 0

theorem assocBCA_eq : associatorZ 2 7 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 7 3) (RightIndex 2 3 7) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 3 7 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21759556,
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

def assocCAB : Matrix (RightIndex 7 3 2) (LeftIndex 7 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 7 3 2 r) []).getD (leftPosition 7 3 2 s) 0

theorem assocCAB_eq : associatorZ 7 3 2 = assocCAB := by
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

def outerLeftABC : Matrix (RightIndex 7 3 2) (LeftIndex 3 2 7) ℤ :=
  fun r s => ((outerLeftABCRows).getD (rightPosition 7 3 2 r) []).getD (leftPosition 3 2 7 s) 0

theorem outerLeftABC_eq : outerLeftZ 3 2 7 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms327
