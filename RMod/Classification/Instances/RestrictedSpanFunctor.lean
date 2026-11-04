import RMod.Classification.Instances.SuperfunctorHomogeneousSums
import RMod.Classification.Instances.SpanSuperfunctor

/-!
# Restricting a superfunctor to the homogeneous span of an object

Map the underlying object and every ambient morphism by the given
superfunctor. Preservation of specified homogeneous sums supplies the
membership proof. Functoriality, linearity and grading remain separate
laws on this unchanged object-and-map data.
-/

set_option autoImplicit false

namespace RMod.Classification.Superfunctor

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} (F : Superfunctor C D) (S : C.data.Obj)

def restrictSpanData : SpanSuperfunctorData C D S (F.data.obj S) where
  obj X := ⟨F.data.obj X.obj, F.map_homogeneousSpan X.property⟩
  map f := ObjectProperty.homMk (F.data.map f.hom)

theorem restrictSpanLaws : SpanSuperfunctorLaws C D S (F.data.obj S) (F.restrictSpanData S) where
  map_id X := ObjectProperty.hom_ext _ (F.laws.map_id X.obj)
  map_comp f g := ObjectProperty.hom_ext _ (F.laws.map_comp f.hom g.hom)
  map_zero X Y := ObjectProperty.hom_ext _ (F.laws.map_zero X.obj Y.obj)
  map_add f g := ObjectProperty.hom_ext _ (F.laws.map_add f.hom g.hom)
  map_smul r f := ObjectProperty.hom_ext _ (F.laws.map_smul r f.hom)
  map_grade f hf := F.laws.map_grade f.hom hf

def restrictSpan : SpanSuperfunctor C D S (F.data.obj S) :=
  ⟨F.restrictSpanData S, F.restrictSpanLaws S⟩

end RMod.Classification.Superfunctor
