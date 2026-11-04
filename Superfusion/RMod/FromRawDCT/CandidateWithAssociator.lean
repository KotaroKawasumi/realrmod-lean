import Superfusion.RMod.FromRawDCT.Candidate

/-!
# Raw-DCT candidate data with an explicit associator choice

The finite coordinate category, tensor product, unit, and unitors are fixed
by the raw `D`, `C`, and the selected unit rows.  The endpoint convention of
the associator is an additional executable choice.  This abstract data-only
adapter accepts that choice explicitly; it contains no concrete real table
and no coherence proof.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace Candidate

/-- The proof-free coordinate candidate with a supplied executable
associator.  No law is bundled into this definition. -/
def dataWithAssociator (x : RawDCTData) (rows : UnitRowsData x.D x.C)
    (associator : AssociatorData x.D (Tensor.canonicalData x.D x.C)) :
    Superfusion.CandidateData where
  Obj := Obj
  Hom := Hom x.D
  id := Hom.id x.D
  comp := Hom.comp
  zero := Hom.zero x.D _ _
  add := Hom.add
  neg := Hom.neg
  smul := Hom.smul
  grade := fun _ _ a => {f | Hom.MemGrade a f}
  tensorObj := (Tensor.canonicalData x.D x.C).tensorObj
  tensorHom := (Tensor.canonicalData x.D x.C).tensorHom
  tensorUnit := (Unitor.canonicalData x rows).tensorUnit
  associatorHom := associator.associatorHom
  associatorInv := associator.associatorInv
  leftUnitorHom := (Unitor.canonicalData x rows).leftUnitorHom
  leftUnitorInv := (Unitor.canonicalData x rows).leftUnitorInv
  rightUnitorHom := (Unitor.canonicalData x rows).rightUnitorHom
  rightUnitorInv := (Unitor.canonicalData x rows).rightUnitorInv

end Candidate

end Superfusion.RMod.FromRawDCT
