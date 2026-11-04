import Superfusion.RMod.FromRawDCT.Unitor
import Superfusion.WeaklyPointedSuperfusion.CandidateData

/-!
# Weakly-pointed-superfusion candidate data from a raw DCT

This file is the data-only adapter from the finite coordinate construction
to the project's proof-free `CandidateData` boundary.  It accepts arbitrary
raw DCT data together with executable unit rows.  No real instance and no
category, tensor, coherence, finiteness, rigidity, or weak-pointedness proof
is constructed here.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace Candidate

/-- The proof-free finite coordinate candidate extracted from `x`.

When `x` is already shifted, every binary and ternary operation below reads
that shifted `C` and `T` exactly once; there is no later cochain transport. -/
def data (x : RawDCTData) (rows : UnitRowsData x.D x.C) :
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
  associatorHom := (Associator.canonicalData x).associatorHom
  associatorInv := (Associator.canonicalData x).associatorInv
  leftUnitorHom := (Unitor.canonicalData x rows).leftUnitorHom
  leftUnitorInv := (Unitor.canonicalData x rows).leftUnitorInv
  rightUnitorHom := (Unitor.canonicalData x rows).rightUnitorHom
  rightUnitorInv := (Unitor.canonicalData x rows).rightUnitorInv

end Candidate

end Superfusion.RMod.FromRawDCT
