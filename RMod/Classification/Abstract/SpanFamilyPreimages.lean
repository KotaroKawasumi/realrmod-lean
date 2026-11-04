import RMod.Classification.Abstract.SpanFamily
import RMod.Classification.Abstract.Normalizers

/-!
# Specified even preimages for a family realization functor

The preimage family and both comparison maps are retained as data for
every object. The laws assert evenness and the two inverse identities
on precisely those maps. These witnesses will define an actual inverse.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) {I : Type} (S : I → C.data.Obj)

structure SpanFamilyPreimagesData (F : Prefunctor (SpanFamilyCategory C S) (LinearCategory C)) where
  family : C.data.Obj → SpanFamilyCategory C S
  iso : ∀ X, IsoData C.data (F.obj (family X)) X

structure SpanFamilyPreimagesLaws {F : Prefunctor (SpanFamilyCategory C S) (LinearCategory C)}
    (d : SpanFamilyPreimagesData C S F) : Prop where
  evenIso : ∀ X, EvenIsoLaws C.data (d.iso X)

structure SpanFamilyPreimages (F : SpanFamilyCategory C S ⥤ LinearCategory C) where
  data : SpanFamilyPreimagesData C S F.toPrefunctor
  laws : SpanFamilyPreimagesLaws C S data

end RMod.Classification
