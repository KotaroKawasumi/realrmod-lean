import RMod.Classification.Abstract.SpanNatural

/-!
# Invertible homogeneous natural comparisons

Both families of component maps are data. Signed naturality, degree,
and the two pointwise inverse identities are laws on those families.
The source and target are completed superfunctors on completed ambient
categories, as for every other comparison interface.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

structure SpanHomogeneousNatIsoData (F G : SpanSuperfunctorData C D S T)
    extends SpanHomogeneousNatData F G where
  inv : SpanHomogeneousNatData G F

structure SpanHomogeneousNatIsoLaws {F G : SpanSuperfunctorData C D S T} (a : ZMod 2)
    (d : SpanHomogeneousNatIsoData F G) : Prop
    extends SpanHomogeneousNatLaws a d.toSpanHomogeneousNatData where
  inverse : SpanHomogeneousNatLaws a d.inv
  hom_inv : ∀ X, d.app X ≫ d.inv.app X = 𝟙 _
  inv_hom : ∀ X, d.inv.app X ≫ d.app X = 𝟙 _

structure SpanHomogeneousNatIso (F G : SpanSuperfunctor C D S T) (a : ZMod 2) where
  data : SpanHomogeneousNatIsoData F.data G.data
  laws : SpanHomogeneousNatIsoLaws a data

end RMod.Classification
