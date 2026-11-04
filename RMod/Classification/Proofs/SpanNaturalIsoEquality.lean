import RMod.Classification.Abstract.SpanNaturalIso

/-!
# Equality transport retains the raw component maps

When completed component functors are identified, transporting a natural
isomorphism changes only the endpoint types of its maps. Heterogeneous
equality records the original forward and inverse maps without erasing
the object equalities needed later for indexed evaluation.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNatIso

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {S : A.data.Obj} {T : C.data.Obj}
  {F G F' G' : SpanSuperfunctor A C S T} {a : ZMod 2}

theorem app_raw_heq (hF : F = F') (hG : G = G')
    {η : SpanHomogeneousNatIso F G a} {θ : SpanHomogeneousNatIso F' G' a}
    (he : HEq η θ) (X : HomogeneousSpanCategory A S) :
    HEq (η.data.app X).hom (θ.data.app X).hom := by
  cases hF
  cases hG
  cases he
  rfl

theorem inv_raw_heq (hF : F = F') (hG : G = G')
    {η : SpanHomogeneousNatIso F G a} {θ : SpanHomogeneousNatIso F' G' a}
    (he : HEq η θ) (X : HomogeneousSpanCategory A S) :
    HEq (η.data.inv.app X).hom (θ.data.inv.app X).hom := by
  cases hF
  cases hG
  cases he
  rfl

end RMod.Classification.SpanHomogeneousNatIso
