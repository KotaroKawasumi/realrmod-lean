import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms312
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 22035118,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 26129182,
    decodeIntegerRow 16 3 1 21521164,
    decodeIntegerRow 16 3 1 21524116,
    decodeIntegerRow 16 3 1 21523116,
    decodeIntegerRow 16 3 1 21523444,
    decodeIntegerRow 16 3 1 20972236,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 16563244,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 21524062,
    decodeIntegerRow 16 3 1 21521182,
    decodeIntegerRow 16 3 1 21523438,
    decodeIntegerRow 16 3 1 21523118]

def assocABC : Matrix (RightIndex 3 1 2) (LeftIndex 3 1 2) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 3 1 2 r) []).getD (leftPosition 3 1 2 s) 0

theorem assocABC_eq : associatorZ 3 1 2 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def outerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35170732,
    decodeIntegerRow 16 3 1 15222504,
    decodeIntegerRow 16 3 1 18371948,
    decodeIntegerRow 16 3 1 6825736,
    decodeIntegerRow 16 3 1 7876972,
    decodeIntegerRow 16 3 1 27819624,
    decodeIntegerRow 16 3 1 24670508,
    decodeIntegerRow 16 3 1 36219016,
    decodeIntegerRow 16 3 1 15065096,
    decodeIntegerRow 16 3 1 35511892,
    decodeIntegerRow 16 3 1 6458344,
    decodeIntegerRow 16 3 1 18293268,
    decodeIntegerRow 16 3 1 15069576,
    decodeIntegerRow 16 3 1 35510932,
    decodeIntegerRow 16 3 1 6460264,
    decodeIntegerRow 16 3 1 18297428]

def outerABC : Matrix (LeftIndex 1 2 3) (RightIndex 3 1 2) ℤ :=
  fun r s => ((outerABCRows).getD (leftPosition 1 2 3 r) []).getD (rightPosition 3 1 2 s) 0

theorem outerABC_eq : outerRightZ 3 1 2 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBACRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21525556,
    decodeIntegerRow 16 3 1 21522604,
    decodeIntegerRow 16 3 1 21523604,
    decodeIntegerRow 16 3 1 21523276,
    decodeIntegerRow 16 3 1 20972236,
    decodeIntegerRow 16 3 1 19922476,
    decodeIntegerRow 16 3 1 16563244,
    decodeIntegerRow 16 3 1 7115404,
    decodeIntegerRow 16 3 1 22035118,
    decodeIntegerRow 16 3 1 23111122,
    decodeIntegerRow 16 3 1 26129182,
    decodeIntegerRow 16 3 1 35813218,
    decodeIntegerRow 16 3 1 21525538,
    decodeIntegerRow 16 3 1 21522658,
    decodeIntegerRow 16 3 1 21523602,
    decodeIntegerRow 16 3 1 21523282]

def assocBAC : Matrix (RightIndex 1 3 2) (LeftIndex 1 3 2) ℤ :=
  fun r s => ((assocBACRows).getD (rightPosition 1 3 2 r) []).getD (leftPosition 1 3 2 s) 0

theorem assocBAC_eq : associatorZ 1 3 2 = assocBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerABC : Matrix (LeftIndex 1 3 2) (LeftIndex 3 1 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerABC_eq : innerLeftZ 3 1 2 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21521066,
    decodeIntegerRow 16 3 1 21523858,
    decodeIntegerRow 16 3 1 21522394,
    decodeIntegerRow 16 3 1 21521282,
    decodeIntegerRow 16 3 1 21525602,
    decodeIntegerRow 16 3 1 21522886,
    decodeIntegerRow 16 3 1 21524338,
    decodeIntegerRow 16 3 1 21525494,
    decodeIntegerRow 16 3 1 7889602,
    decodeIntegerRow 16 3 1 27861286,
    decodeIntegerRow 16 3 1 24790738,
    decodeIntegerRow 16 3 1 36574294,
    decodeIntegerRow 16 3 1 7522186,
    decodeIntegerRow 16 3 1 27940018,
    decodeIntegerRow 16 3 1 24633274,
    decodeIntegerRow 16 3 1 36233122]

def innerRightABC : Matrix (RightIndex 3 2 1) (RightIndex 3 1 2) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 3 2 1 r) []).getD (rightPosition 3 1 2 s) 0

theorem innerRightABC_eq : innerRightZ 3 1 2 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21525440,
    decodeIntegerRow 16 3 1 21522400,
    decodeIntegerRow 16 3 1 21522880,
    decodeIntegerRow 16 3 1 21521120,
    decodeIntegerRow 16 3 1 35170240,
    decodeIntegerRow 16 3 1 15224800,
    decodeIntegerRow 16 3 1 18374080,
    decodeIntegerRow 16 3 1 6826720,
    decodeIntegerRow 16 3 1 21523852,
    decodeIntegerRow 16 3 1 21521064,
    decodeIntegerRow 16 3 1 21521228,
    decodeIntegerRow 16 3 1 21522376,
    decodeIntegerRow 16 3 1 18295348,
    decodeIntegerRow 16 3 1 36587416,
    decodeIntegerRow 16 3 1 35511412,
    decodeIntegerRow 16 3 1 27979384]

def inverseACB : Matrix (LeftIndex 3 2 1) (RightIndex 3 2 1) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 3 2 1 r) []).getD (rightPosition 3 2 1 s) 0

theorem inverseACB_eq : associatorInverseZ 3 2 1 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 2 3 1) (LeftIndex 3 2 1) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerACB_eq : innerLeftZ 3 2 1 = innerACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocBCARows : List (List ℤ) := [decodeIntegerRow 16 3 1 35169748,
    decodeIntegerRow 16 3 1 15227096,
    decodeIntegerRow 16 3 1 18376212,
    decodeIntegerRow 16 3 1 6827704,
    decodeIntegerRow 16 3 1 15065096,
    decodeIntegerRow 16 3 1 35511892,
    decodeIntegerRow 16 3 1 6458344,
    decodeIntegerRow 16 3 1 18293268,
    decodeIntegerRow 16 3 1 15222504,
    decodeIntegerRow 16 3 1 35170732,
    decodeIntegerRow 16 3 1 6825736,
    decodeIntegerRow 16 3 1 18371948,
    decodeIntegerRow 16 3 1 7535788,
    decodeIntegerRow 16 3 1 27977144,
    decodeIntegerRow 16 3 1 24749292,
    decodeIntegerRow 16 3 1 36586456]

def assocBCA : Matrix (RightIndex 1 2 3) (LeftIndex 1 2 3) ℤ :=
  fun r s => ((assocBCARows).getD (rightPosition 1 2 3 r) []).getD (leftPosition 1 2 3 s) 0

theorem assocBCA_eq : associatorZ 1 2 3 = assocBCA := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerRightBAC : Matrix (RightIndex 1 2 3) (RightIndex 1 3 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem innerRightBAC_eq : innerRightZ 1 3 2 = innerRightBAC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def assocCABRows : List (List ℤ) := [decodeIntegerRow 16 3 1 26306338,
    decodeIntegerRow 16 3 1 7174426,
    decodeIntegerRow 16 3 1 22054802,
    decodeIntegerRow 16 3 1 19929034,
    decodeIntegerRow 16 3 1 35872240,
    decodeIntegerRow 16 3 1 16740400,
    decodeIntegerRow 16 3 1 23117680,
    decodeIntegerRow 16 3 1 20991920,
    decodeIntegerRow 16 3 1 21542800,
    decodeIntegerRow 16 3 1 21529840,
    decodeIntegerRow 16 3 1 21698320,
    decodeIntegerRow 16 3 1 21581680,
    decodeIntegerRow 16 3 1 21516718,
    decodeIntegerRow 16 3 1 21503434,
    decodeIntegerRow 16 3 1 21463582,
    decodeIntegerRow 16 3 1 21344026]

def assocCAB : Matrix (RightIndex 2 3 1) (LeftIndex 2 3 1) ℤ :=
  fun r s => ((assocCABRows).getD (rightPosition 2 3 1 r) []).getD (leftPosition 2 3 1 s) 0

theorem assocCAB_eq : associatorZ 2 3 1 = assocCAB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerLeftABC : Matrix (RightIndex 2 3 1) (LeftIndex 3 1 2) ℤ :=
  (show Matrix (Fin 2 × Fin 2 × Fin 4) (Fin 2 × Fin 2 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 3 1 2 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms312
