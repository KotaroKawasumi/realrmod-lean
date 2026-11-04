import RMod.Classification.Abstract.SpanSuperequivalence
import RMod.Classification.Proofs.HomogeneousSpanChange

/-!
# Identity equivalences between equal homogeneous spans

Mathlib's inclusion functors for object properties retain each ambient
object and morphism. When the two properties are equivalent they are
mutual inverses, with identity unit and counit. Their additional
superlinear laws are separate and hold for the unchanged maps.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (C : WeaklyPointedSuperfusion.{0, 0}) {S T : C.data.Obj}

theorem spanInclusionLaws (h : InHomogeneousSpan C S ≤ InHomogeneousSpan C T) :
    SpanSuperfunctorLaws C C S T (ObjectProperty.ιOfLE h).toPrefunctor where
  map_id _ := rfl
  map_comp _ _ := rfl
  map_zero _ _ := rfl
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_grade _ hf := hf

def spanChangeEquivalenceData (h : ∀ X, InHomogeneousSpan C S X ↔ InHomogeneousSpan C T X) :
    SpanSuperequivalenceData C C S T where
  functor := ObjectProperty.ιOfLE (fun X hX => (h X).mp hX)
  inverse := ObjectProperty.ιOfLE (fun X hX => (h X).mpr hX)
  unitIso := NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Iso.refl X.obj)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact (C.laws.comp_id f.hom).trans (C.laws.id_comp f.hom).symm)
  counitIso := NatIso.ofComponents (fun X => ObjectProperty.isoMk _ (Iso.refl X.obj)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact (C.laws.comp_id f.hom).trans (C.laws.id_comp f.hom).symm)
  functor_unitIso_comp X := by
    apply ObjectProperty.hom_ext
    exact C.laws.comp_id (C.data.id X.obj)

theorem spanChangeEquivalenceLaws (h : ∀ X, InHomogeneousSpan C S X ↔ InHomogeneousSpan C T X) :
    SpanSuperequivalenceLaws C C S T (spanChangeEquivalenceData C h) where
  forward := spanInclusionLaws C (fun X hX => (h X).mp hX)
  backward := spanInclusionLaws C (fun X hX => (h X).mpr hX)
  unit_hom_even X := C.laws.id_even X.obj
  unit_inv_even X := C.laws.id_even X.obj
  counit_hom_even X := C.laws.id_even X.obj
  counit_inv_even X := C.laws.id_even X.obj

def spanChangeSuperequivalence (h : ∀ X, InHomogeneousSpan C S X ↔ InHomogeneousSpan C T X) :
    SpanSuperequivalence C C S T :=
  ⟨spanChangeEquivalenceData C h, spanChangeEquivalenceLaws C h⟩

end RMod.Classification
