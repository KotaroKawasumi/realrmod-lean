import RMod.Classification.Abstract.SpanNaturalIso

/-!
# The maps of an invertible homogeneous comparison

These views retain the specified forward and inverse natural maps. At
each object the same data and inverse laws give a Mathlib isomorphism.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNatIso

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T} {a : ZMod 2}

def hom (η : SpanHomogeneousNatIso F G a) : SpanHomogeneousNat F G a :=
  ⟨η.data.toSpanHomogeneousNatData, η.laws.toSpanHomogeneousNatLaws⟩

def inverse (η : SpanHomogeneousNatIso F G a) : SpanHomogeneousNat G F a :=
  ⟨η.data.inv, η.laws.inverse⟩

def appIso (η : SpanHomogeneousNatIso F G a) (X : HomogeneousSpanCategory C S) :
    F.data.obj X ≅ G.data.obj X :=
  ⟨η.data.app X, η.data.inv.app X, η.laws.hom_inv X, η.laws.inv_hom X⟩

end RMod.Classification.SpanHomogeneousNatIso
