import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms322
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35878828,
    decodeIntegerRow 16 3 1 26326012,
    decodeIntegerRow 16 3 1 21523468,
    decodeIntegerRow 16 3 1 21523612,
    decodeIntegerRow 16 3 1 22231948,
    decodeIntegerRow 16 3 1 23176732,
    decodeIntegerRow 16 3 1 21525548,
    decodeIntegerRow 16 3 1 21524092,
    decodeIntegerRow 16 3 1 26286646,
    decodeIntegerRow 16 3 1 35865706,
    decodeIntegerRow 16 3 1 21523594,
    decodeIntegerRow 16 3 1 21523414,
    decodeIntegerRow 16 3 1 19988086,
    decodeIntegerRow 16 3 1 21169066,
    decodeIntegerRow 16 3 1 21522634,
    decodeIntegerRow 16 3 1 21521174]

def assocABC : Matrix (RightIndex 3 2 2) (LeftIndex 3 2 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 2 2 r) []).getD (leftPosition 3 2 2 s) 0

theorem assocABC_eq : associatorZ 3 2 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 2 2 3) (RightIndex 3 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerABC_eq : outerRightZ 3 2 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 21169318,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22231714,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7168618,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 23176786]

def assocBAC : Matrix (RightIndex 2 3 2) (LeftIndex 2 3 2) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 2 3 2 r) []).getD (leftPosition 2 3 2 s) 0

theorem assocBAC_eq : associatorZ 2 3 2 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 2 3 2) (LeftIndex 3 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 2 2 = innerABC := by
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
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 21529921,
    decodeIntegerRow 16 3 1 21543043,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453,
    decodeIntegerRow 16 3 1 22054801,
    decodeIntegerRow 16 3 1 23117683]

def innerRightABC : Matrix (RightIndex 3 2 2) (RightIndex 3 2 2) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 3 2 2 r) []).getD (rightPosition 3 2 2 s) 0

theorem innerRightABC_eq : innerRightZ 3 2 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35872996,
    decodeIntegerRow 16 3 1 26308516,
    decodeIntegerRow 16 3 1 21464338,
    decodeIntegerRow 16 3 1 21346222,
    decodeIntegerRow 16 3 1 21700516,
    decodeIntegerRow 16 3 1 21582436,
    decodeIntegerRow 16 3 1 16742578,
    decodeIntegerRow 16 3 1 7175182,
    decodeIntegerRow 16 3 1 21503678,
    decodeIntegerRow 16 3 1 21516802,
    decodeIntegerRow 16 3 1 22055044,
    decodeIntegerRow 16 3 1 23117764,
    decodeIntegerRow 16 3 1 19929118,
    decodeIntegerRow 16 3 1 20992162,
    decodeIntegerRow 16 3 1 21529924,
    decodeIntegerRow 16 3 1 21543044]

def inverseACB : Matrix (LeftIndex 3 2 2) (RightIndex 3 2 2) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 2 2 r) []).getD (rightPosition 3 2 2 s) 0

theorem inverseACB_eq : associatorInverseZ 3 2 2 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 3 2) (LeftIndex 3 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 2 2 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 19929064,
    decodeIntegerRow 16 3 1 20991928,
    decodeIntegerRow 16 3 1 21529192,
    decodeIntegerRow 16 3 1 21540856,
    decodeIntegerRow 16 3 1 21501490,
    decodeIntegerRow 16 3 1 21516070,
    decodeIntegerRow 16 3 1 22054810,
    decodeIntegerRow 16 3 1 23117710,
    decodeIntegerRow 16 3 1 21346456,
    decodeIntegerRow 16 3 1 21464392,
    decodeIntegerRow 16 3 1 26306328,
    decodeIntegerRow 16 3 1 35872264,
    decodeIntegerRow 16 3 1 7174450,
    decodeIntegerRow 16 3 1 16740390,
    decodeIntegerRow 16 3 1 21582490,
    decodeIntegerRow 16 3 1 21700750]

def assocBCA : Matrix (RightIndex 2 2 3) (LeftIndex 2 2 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 2 2 3 r) []).getD (leftPosition 2 2 3 s) 0

theorem assocBCA_eq : associatorZ 2 2 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 2 2 3) (RightIndex 2 3 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 2 3 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21877906,
    decodeIntegerRow 16 3 1 23058742,
    decodeIntegerRow 16 3 1 26284458,
    decodeIntegerRow 16 3 1 35864974,
    decodeIntegerRow 16 3 1 7180282,
    decodeIntegerRow 16 3 1 16757886,
    decodeIntegerRow 16 3 1 19988194,
    decodeIntegerRow 16 3 1 21169318,
    decodeIntegerRow 16 3 1 23176678,
    decodeIntegerRow 16 3 1 22231714,
    decodeIntegerRow 16 3 1 7167166,
    decodeIntegerRow 16 3 1 16718522,
    decodeIntegerRow 16 3 1 16722894,
    decodeIntegerRow 16 3 1 7168618,
    decodeIntegerRow 16 3 1 22232182,
    decodeIntegerRow 16 3 1 23176786]

def assocCAB : Matrix (RightIndex 2 3 2) (LeftIndex 2 3 2) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 2 3 2 r) []).getD (leftPosition 2 3 2 s) 0

theorem assocCAB_eq : associatorZ 2 3 2 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 2 3 2) (LeftIndex 3 2 2) ℤ :=
  (show Matrix (Fin 2 × Fin 4 × Fin 2) (Fin 2 × Fin 4 × Fin 2) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 2 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms322
