import Superfusion.RMod.FromRawDCT.CandidateCompletionWithAssociator
import Superfusion.RMod.FromRawDCT.RealUnitorLaws
import Superfusion.RMod.FromRawDCT.RealCandidateInvariantLaws
import Superfusion.RMod.FromRawDCT.RealPairingWithAssociator
import Superfusion.WeaklyPointedSuperfusion.Basic

/-!
# Computable finite-coordinate real RMod

This final assembly bundles the executable finite coordinate candidate of
the computably shifted real raw DCT into a weakly pointed superfusion
category.  Every law is proved directly on the finite coordinates: the
associator laws come from the completed pentagon file, the unitor laws
from the completed triangle file, the invariant laws from the re-bundled
finite witnesses, and the duality and weak-pointedness witnesses from the
raw pairing construction over the same endpoint-normalized associator.

No semantic category is consulted and no reflection bridge is used.  No
table is evaluated in this assembly file.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Data, laws, and completed structure -/

/-- Executable finite-coordinate RMod data obtained from the computably
shifted real raw DCT with its endpoint-normalized associator. -/
def realComputableRModData : Superfusion.CandidateData :=
  realEndpointCandidateData

set_option maxHeartbeats 1600000 in
/-- All weakly pointed superfusion laws for the exact executable data
above, assembled by the associator-parametric candidate completion. -/
theorem realComputableRModLaws :
    Superfusion.CandidateLaws realComputableRModData :=
  Candidate.completionLawsWithAssociator
    realComputableShiftedRawDCT.data
    realComputableShiftedRawDCT.laws
    realUnitRowsData
    realAssociatorData
    realAssociatorLaws
    realUnitorLaws
    RealCandidateInvariantLaws.hasFiniteBiproducts
    RealCandidateInvariantLaws.semisimple
    RealCandidateInvariantLaws.gradedSchur
    RealCandidateInvariantLaws.finiteDimensionalHom
    RealCandidateInvariantLaws.finiteSimpleRepresentatives
    RealCandidateInvariantLaws.simpleUnit
    RealCandidateInvariantLaws.unitEndScalarInjective
    RealCandidateInvariantLaws.unitEndScalarSurjective
    (RealPairingWithAssociator.raw_has_right_dual
      realAssociatorLaws realUnitorLaws)
    (RealPairingWithAssociator.raw_has_left_dual
      realAssociatorLaws realUnitorLaws)
    (RealPairingWithAssociator.raw_weaklyPointed
      realAssociatorLaws realUnitorLaws)

/-- The finite-coordinate real regular module, bundled as a weakly pointed
superfusion category over exact executable data. -/
def realComputableRMod :
    Superfusion.WeaklyPointedSuperfusionCategory where
  data := realComputableRModData
  laws := realComputableRModLaws

/-! ## Closed nontrivial evaluations -/

/-- The bundled tensor keeps the odd binary regrading at `(1,1)`. -/
example :
    Atom.shift
      ((realComputableRMod.data.tensorObj
        (Obj.singleton (1, 0)) (Obj.singleton (1, 0))).atom
          ⟨0, by change 0 < 1; omega⟩) = 1 :=
  rfl

/-- The bundled `(1,3)` tensor retains its two distinct fusion rows. -/
example :
    (realComputableRMod.data.tensorObj
      (Obj.singleton (1, 0)) (Obj.singleton (3, 0))).size = 2 :=
  rfl

end Superfusion.RMod.FromRawDCT
