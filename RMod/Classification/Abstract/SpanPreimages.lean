import RMod.Classification.Abstract.SpanSuperfunctor
import RMod.Classification.Abstract.Normalizers

/-!
# Even object preimages for a fully faithful span functor

Preimage objects and the two counit maps are computational data. Their
inverse identities and evenness are separate laws. Storing even maps here
ensures that the subsequent inverse functor respects the superstructure.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}

structure SpanPreimagesData (F : SpanSuperfunctorData C D S T) where
  object : HomogeneousSpanCategory D T → HomogeneousSpanCategory C S
  counit : (Y : HomogeneousSpanCategory D T) → IsoData D.data (F.obj (object Y)).obj Y.obj

structure SpanPreimagesLaws {F : SpanSuperfunctorData C D S T} (d : SpanPreimagesData F) : Prop where
  counit : ∀ Y, EvenIsoLaws D.data (d.counit Y)

structure SpanPreimages (F : SpanSuperfunctor C D S T) where
  data : SpanPreimagesData F.data
  laws : SpanPreimagesLaws data

end RMod.Classification
