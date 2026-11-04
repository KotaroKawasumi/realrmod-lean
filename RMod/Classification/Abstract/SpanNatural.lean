import RMod.Classification.Abstract.SpanSuperfunctor

/-!
# Homogeneous natural transformations between component superfunctors

The components are morphism data. Their degree and signed naturality
against every homogeneous morphism are laws on these data. Odd natural
transformations must include this sign; an odd object endomorphism alone
does not define an odd natural endomorphism of a functor.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

structure SpanHomogeneousNatData (F G : SpanSuperfunctorData C D S T) where
  app : (X : HomogeneousSpanCategory C S) → F.obj X ⟶ G.obj X

structure SpanHomogeneousNatLaws {F G : SpanSuperfunctorData C D S T} (a : ZMod 2)
    (d : SpanHomogeneousNatData F G) : Prop where
  grade : ∀ X, D.data.IsHomogeneous a (d.app X).hom
  naturality : ∀ {X Y : HomogeneousSpanCategory C S} {b : ZMod 2} (f : X ⟶ Y),
    C.data.IsHomogeneous b f.hom →
      F.map f ≫ d.app Y = ((-1 : ℝ) ^ (a * b).val) • (d.app X ≫ G.map f)

structure SpanHomogeneousNat (F G : SpanSuperfunctor C D S T) (a : ZMod 2) where
  data : SpanHomogeneousNatData F.data G.data
  laws : SpanHomogeneousNatLaws a data

end RMod.Classification
