import RMod.BrundanEllis.StackingReferenceHexagonRowEncoding
import RMod.BrundanEllis.StackingReferenceMatrixCheck

/-! Candidate atomic integer matrices and their independently checked reference equations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option maxErrors 1
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms444
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT

private def assocABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 7115162,
    decodeIntegerRow 16 3 1 16917622,
    decodeIntegerRow 16 3 1 23122066,
    decodeIntegerRow 16 3 1 22035874,
    decodeIntegerRow 16 3 1 16917454,
    decodeIntegerRow 16 3 1 35931074,
    decodeIntegerRow 16 3 1 22034362,
    decodeIntegerRow 16 3 1 19920298,
    decodeIntegerRow 16 3 1 23108926,
    decodeIntegerRow 16 3 1 20971534,
    decodeIntegerRow 16 3 1 35813462,
    decodeIntegerRow 16 3 1 16563322,
    decodeIntegerRow 16 3 1 20972938,
    decodeIntegerRow 16 3 1 19933402,
    decodeIntegerRow 16 3 1 16563166,
    decodeIntegerRow 16 3 1 7233746]

def assocABC : Matrix (RightIndex 4 4 4) (LeftIndex 4 4 4) ℤ :=
  fun r s => ((assocABCRows).getD (rightPosition 4 4 4 r) []).getD (leftPosition 4 4 4 s) 0

theorem assocABC_eq : associatorZ 4 4 4 = assocABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def outerABC : Matrix (LeftIndex 4 4 4) (RightIndex 4 4 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerABC_eq : outerRightZ 4 4 4 = outerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

def assocBAC : Matrix (RightIndex 4 4 4) (LeftIndex 4 4 4) ℤ := assocABC

theorem assocBAC_eq : associatorZ 4 4 4 = assocBAC := assocABC_eq

private def innerABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def innerABC : Matrix (LeftIndex 4 4 4) (LeftIndex 4 4 4) ℤ :=
  fun r s => ((innerABCRows).getD (leftPosition 4 4 4 r) []).getD (leftPosition 4 4 4 s) 0

theorem innerABC_eq : innerLeftZ 4 4 4 = innerABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def innerRightABCRows : List (List ℤ) := [decodeIntegerRow 16 3 1 21523361,
    decodeIntegerRow 16 3 1 21523363,
    decodeIntegerRow 16 3 1 21523369,
    decodeIntegerRow 16 3 1 21523387,
    decodeIntegerRow 16 3 1 21523279,
    decodeIntegerRow 16 3 1 21523117,
    decodeIntegerRow 16 3 1 21522631,
    decodeIntegerRow 16 3 1 21521173,
    decodeIntegerRow 16 3 1 21516799,
    decodeIntegerRow 16 3 1 21503677,
    decodeIntegerRow 16 3 1 21464311,
    decodeIntegerRow 16 3 1 21346213,
    decodeIntegerRow 16 3 1 20991919,
    decodeIntegerRow 16 3 1 19929037,
    decodeIntegerRow 16 3 1 16740391,
    decodeIntegerRow 16 3 1 7174453]

def innerRightABC : Matrix (RightIndex 4 4 4) (RightIndex 4 4 4) ℤ :=
  fun r s => ((innerRightABCRows).getD (rightPosition 4 4 4 r) []).getD (rightPosition 4 4 4 s) 0

theorem innerRightABC_eq : innerRightZ 4 4 4 = innerRightABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

private def inverseACBRows : List (List ℤ) := [decodeIntegerRow 16 3 1 35931560,
    decodeIntegerRow 16 3 1 26129104,
    decodeIntegerRow 16 3 1 19924672,
    decodeIntegerRow 16 3 1 21010900,
    decodeIntegerRow 16 3 1 16917460,
    decodeIntegerRow 16 3 1 35931072,
    decodeIntegerRow 16 3 1 22034416,
    decodeIntegerRow 16 3 1 19920280,
    decodeIntegerRow 16 3 1 23108944,
    decodeIntegerRow 16 3 1 20971480,
    decodeIntegerRow 16 3 1 35813460,
    decodeIntegerRow 16 3 1 16563328,
    decodeIntegerRow 16 3 1 20972992,
    decodeIntegerRow 16 3 1 19933420,
    decodeIntegerRow 16 3 1 16563160,
    decodeIntegerRow 16 3 1 7233744]

def inverseACB : Matrix (LeftIndex 4 4 4) (RightIndex 4 4 4) ℤ :=
  fun r s => ((inverseACBRows).getD (leftPosition 4 4 4 r) []).getD (rightPosition 4 4 4 s) 0

theorem inverseACB_eq : associatorInverseZ 4 4 4 = inverseACB := by
  apply tripleMatrixCheck_sound
  decide +kernel

def innerACB : Matrix (LeftIndex 4 4 4) (LeftIndex 4 4 4) ℤ := innerABC

theorem innerACB_eq : innerLeftZ 4 4 4 = innerACB := innerABC_eq

def assocBCA : Matrix (RightIndex 4 4 4) (LeftIndex 4 4 4) ℤ := assocABC

theorem assocBCA_eq : associatorZ 4 4 4 = assocBCA := assocABC_eq

def innerRightBAC : Matrix (RightIndex 4 4 4) (RightIndex 4 4 4) ℤ := innerRightABC

theorem innerRightBAC_eq : innerRightZ 4 4 4 = innerRightBAC := innerRightABC_eq

def assocCAB : Matrix (RightIndex 4 4 4) (LeftIndex 4 4 4) ℤ := assocABC

theorem assocCAB_eq : associatorZ 4 4 4 = assocCAB := assocABC_eq

def outerLeftABC : Matrix (RightIndex 4 4 4) (LeftIndex 4 4 4) ℤ :=
  (show Matrix (Fin 4 × Fin 1 × Fin 4) (Fin 4 × Fin 1 × Fin 4) ℤ from 1)

theorem outerLeftABC_eq : outerLeftZ 4 4 4 = outerLeftABC := by
  apply tripleMatrixCheck_sound
  decide +kernel

end RMod.BrundanEllis.Stacking.ReferenceCommutor.HexagonAtoms444
