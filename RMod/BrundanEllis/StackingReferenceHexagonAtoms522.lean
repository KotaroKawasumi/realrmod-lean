import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms522
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23058580,
    decodeIntegerRow 16 3 1 20814520,
    decodeIntegerRow 16 3 1 26323824,
    decodeIntegerRow 16 3 1 35866432,
    decodeIntegerRow 16 3 1 35864980,
    decodeIntegerRow 16 3 1 16718520,
    decodeIntegerRow 16 3 1 22231696,
    decodeIntegerRow 16 3 1 23058688,
    decodeIntegerRow 16 3 1 7167160,
    decodeIntegerRow 16 3 1 26284460,
    decodeIntegerRow 16 3 1 21877888,
    decodeIntegerRow 16 3 1 23176624,
    decodeIntegerRow 16 3 1 23176840,
    decodeIntegerRow 16 3 1 21169300,
    decodeIntegerRow 16 3 1 16757888,
    decodeIntegerRow 16 3 1 7168624]

def assocABC : Matrix (RightIndex 5 2 2) (LeftIndex 5 2 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 5 2 2 r) []).getD (leftPosition 5 2 2 s) 0

theorem assocABC_eq : associatorZ 5 2 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 2 5) (RightIndex 5 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 5 2 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 19869934,
    decodeIntegerRow 16 3 1 21877402,
    decodeIntegerRow 16 3 1 35878102,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 16762262,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 23058526,
    decodeIntegerRow 16 3 1 26323826,
    decodeIntegerRow 16 3 1 35866438,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 20815006]

def assocBAC : Matrix (RightIndex 2 5 2) (LeftIndex 2 5 2) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 5 2 r) []).getD (leftPosition 2 5 2 s) 0

theorem assocBAC_eq : associatorZ 2 5 2 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 5 2) (LeftIndex 5 2 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 5 2 2 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523603,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21525547,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523359,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523351,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 26306329,
    decodeIntegerRow 16 3 1 35872267,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037]

def innerRightABC : Matrix (RightIndex 5 2 2) (RightIndex 5 2 2) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 5 2 2 r) []).getD (rightPosition 5 2 2 s) 0

theorem innerRightABC_eq : innerRightZ 5 2 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26325760,
    decodeIntegerRow 16 3 1 35865760,
    decodeIntegerRow 16 3 1 19869256,
    decodeIntegerRow 16 3 1 21875468,
    decodeIntegerRow 16 3 1 21879840,
    decodeIntegerRow 16 3 1 23176000,
    decodeIntegerRow 16 3 1 35865652,
    decodeIntegerRow 16 3 1 16720456,
    decodeIntegerRow 16 3 1 7167784,
    decodeIntegerRow 16 3 1 26286412,
    decodeIntegerRow 16 3 1 22229760,
    decodeIntegerRow 16 3 1 23059360,
    decodeIntegerRow 16 3 1 19988812,
    decodeIntegerRow 16 3 1 22234136,
    decodeIntegerRow 16 3 1 16759840,
    decodeIntegerRow 16 3 1 7168000]

def inverseACB : Matrix (LeftIndex 5 2 2) (RightIndex 5 2 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 5 2 2 r) []).getD (rightPosition 5 2 2 s) 0

theorem inverseACB_eq : associatorInverseZ 5 2 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 5 2) (LeftIndex 5 2 2) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 5 2 2 = innerACB := innerABC_eq

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 20812586,
    decodeIntegerRow 16 3 1 19988818,
    decodeIntegerRow 16 3 1 7167946,
    decodeIntegerRow 16 3 1 26286898,
    decodeIntegerRow 16 3 1 26286394,
    decodeIntegerRow 16 3 1 35878882,
    decodeIntegerRow 16 3 1 19987354,
    decodeIntegerRow 16 3 1 22229762,
    decodeIntegerRow 16 3 1 23177458,
    decodeIntegerRow 16 3 1 21171254,
    decodeIntegerRow 16 3 1 26325778,
    decodeIntegerRow 16 3 1 35865814,
    decodeIntegerRow 16 3 1 7181122,
    decodeIntegerRow 16 3 1 26326246,
    decodeIntegerRow 16 3 1 21879842,
    decodeIntegerRow 16 3 1 23176006]

def assocBCA : Matrix (RightIndex 2 2 5) (LeftIndex 2 2 5) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 2 5 r) []).getD (leftPosition 2 2 5 s) 0

theorem assocBCA_eq : associatorZ 2 2 5 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 2 5) (RightIndex 2 5 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 5 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocCAB : Matrix (RightIndex 2 5 2) (LeftIndex 2 5 2) ℤ := assocBAC

theorem assocCAB_eq : associatorZ 2 5 2 = assocCAB := assocBAC_eq

def outerLeftABC : Matrix (RightIndex 2 5 2) (LeftIndex 5 2 2) ℤ :=
  (show Matrix (Fin 4 × Fin 2 × Fin 2) (Fin 4 × Fin 2 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 5 2 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms522
