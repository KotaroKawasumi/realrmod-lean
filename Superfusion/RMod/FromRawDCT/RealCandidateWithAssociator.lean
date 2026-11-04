import Superfusion.RMod.FromRawDCT.CandidateWithAssociator
import Superfusion.RMod.FromRawDCT.RealAssociator
import Superfusion.RMod.FromRawDCT.RealCandidate

/-!
# Concrete real candidate with endpoint-normalized associator

This concrete data file inserts `realAssociatorData` into the finite
coordinate candidate of the computably shifted real raw DCT.  It contains
no coherence proof and does not alter the earlier canonical presentation.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Proof-free concrete data -/

/-- The executable finite coordinate candidate whose associator uses the
endpoint convention required by shifted-coordinate naturality. -/
def realEndpointCandidateData : Superfusion.CandidateData :=
  Candidate.dataWithAssociator realComputableShiftedRawDCT.data
    realUnitRowsData realAssociatorData

/-! ## Closed nontrivial evaluations -/

/-- The corrected candidate retains the nonzero binary regrading at
`(1,1)`. -/
example :
    Atom.shift
      ((realEndpointCandidateData.tensorObj
        (Obj.singleton (1, 0)) (Obj.singleton (1, 0))).atom
          ⟨0, by change 0 < 1; omega⟩) = 1 :=
  rfl

/-- The corrected candidate retains both fusion rows on the nontrivial
`(1,3)` face. -/
example :
    (realEndpointCandidateData.tensorObj
      (Obj.singleton (1, 0)) (Obj.singleton (3, 0))).size = 2 :=
  rfl

end Superfusion.RMod.FromRawDCT
