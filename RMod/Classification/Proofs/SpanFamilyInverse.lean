import RMod.Classification.Instances.SpanFamilyInverse

/-!
# Grading of the specified inverse and its unit

Degree reflection by the realization functor determines the degree of
its unique preimages. Conjugating by the retained even counit then
preserves degree. The unit and its inverse are lifts of even maps.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanFamilyPreimages

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {I : Type} {S : I → C.data.Obj}
  {F : SpanFamilyCategory C S ⥤ LinearCategory C} (p : SpanFamilyPreimages C S F) (hF : F.FullyFaithful)
  (hgrade : ∀ {X Y : SpanFamilyCategory C S} {a : ZMod 2} (f : X ⟶ Y),
    C.data.IsHomogeneous a (F.map f) ↔ ∀ i, C.data.IsHomogeneous a (f i).hom)

include hgrade

theorem preimage_grade {X Y : SpanFamilyCategory C S} {a : ZMod 2}
    (f : F.obj X ⟶ F.obj Y) (hf : C.data.IsHomogeneous a f) (i : I) :
    C.data.IsHomogeneous a (hF.preimage f i).hom := by
  apply (hgrade _).mp _ i
  rwa [hF.map_preimage]

theorem inverseFunctor_map_grade {X Y : LinearCategory C} {a : ZMod 2}
    (f : X ⟶ Y) (hf : C.data.IsHomogeneous a f) (i : I) :
    C.data.IsHomogeneous a ((p.inverseFunctor hF).map f i).hom := by
  apply preimage_grade hF hgrade
  have h := C.laws.comp_grade _ _ (p.laws.evenIso X).hom_even
    (C.laws.comp_grade _ _ hf (p.laws.evenIso Y).inv_even)
  rw [zero_add, add_zero] at h
  exact h

theorem inverseUnitIso_hom_even (X : SpanFamilyCategory C S) (i : I) :
    C.data.IsHomogeneous 0 ((p.inverseUnitIso hF).hom.app X i).hom :=
  preimage_grade hF hgrade _ (p.laws.evenIso (F.obj X)).inv_even i

theorem inverseUnitIso_inv_even (X : SpanFamilyCategory C S) (i : I) :
    C.data.IsHomogeneous 0 ((p.inverseUnitIso hF).inv.app X i).hom :=
  preimage_grade hF hgrade _ (p.laws.evenIso (F.obj X)).hom_even i

end RMod.Classification.SpanFamilyPreimages
