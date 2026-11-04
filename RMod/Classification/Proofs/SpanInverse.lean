import RMod.Classification.Instances.SpanInverse
import RMod.Classification.Abstract.SpanSuperequivalence

/-!
# Linearity and grading of the lifted inverse

Full faithfulness reflects equations. Grading reflection for the forward
functor makes the unique preimages homogeneous. Conjugation by the
specified even counit maps then proves the inverse grading law, and the
unit maps are homogeneous because they lift even counit maps.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanPreimages

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F : SpanSuperfunctor C D S T} (p : SpanPreimages F) (hF : F.toFunctor.FullyFaithful)
  (hgrade : ∀ {X Y : HomogeneousSpanCategory C S} {b : ZMod 2} (f : X ⟶ Y),
    D.data.IsHomogeneous b (F.toFunctor.map f).hom ↔ C.data.IsHomogeneous b f.hom)

include hgrade

theorem preimage_grade {X Y : HomogeneousSpanCategory C S} {b : ZMod 2}
    (f : F.toFunctor.obj X ⟶ F.toFunctor.obj Y) (hf : D.data.IsHomogeneous b f.hom) :
    C.data.IsHomogeneous b (hF.preimage f).hom := by
  apply (hgrade _).mp
  rwa [hF.map_preimage]

theorem inverseFunctorLaws :
    SpanSuperfunctorLaws D C T S (p.inverseFunctor hF).toPrefunctor where
  map_id := (p.inverseFunctor hF).map_id
  map_comp := (p.inverseFunctor hF).map_comp
  map_zero X Y := by
    apply hF.map_injective
    change F.toFunctor.map (hF.preimage ((p.counitIso X).hom ≫ (0 : X ⟶ Y) ≫ (p.counitIso Y).inv)) =
      F.toFunctor.map (0 : p.data.object X ⟶ p.data.object Y)
    simp only [hF.map_preimage, Functor.map_zero,
      Limits.comp_zero, Limits.zero_comp]
  map_add {X Y} f g := by
    apply hF.map_injective
    change F.toFunctor.map (hF.preimage ((p.counitIso X).hom ≫ (f + g) ≫ (p.counitIso Y).inv)) =
      F.toFunctor.map (hF.preimage ((p.counitIso X).hom ≫ f ≫ (p.counitIso Y).inv) +
        hF.preimage ((p.counitIso X).hom ≫ g ≫ (p.counitIso Y).inv))
    simp only [hF.map_preimage, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp]
  map_smul {X Y} r f := by
    apply hF.map_injective
    change F.toFunctor.map (hF.preimage ((p.counitIso X).hom ≫ (r • f) ≫ (p.counitIso Y).inv)) =
      F.toFunctor.map (r • hF.preimage ((p.counitIso X).hom ≫ f ≫ (p.counitIso Y).inv))
    simp only [hF.map_preimage, Functor.map_smul,
      Linear.comp_smul, Linear.smul_comp]
  map_grade {X Y b} f hf := by
    apply preimage_grade hF hgrade
    have hg := D.laws.comp_grade _ _ (p.laws.counit X).hom_even
      (D.laws.comp_grade _ _ hf (p.laws.counit Y).inv_even)
    rw [add_zero, zero_add] at hg
    exact hg

theorem underlyingEquivalenceLaws :
    SpanSuperequivalenceLaws C D S T (p.underlyingEquivalence hF) where
  forward := F.laws
  backward := p.inverseFunctorLaws hF hgrade
  unit_hom_even X := preimage_grade hF hgrade _ (p.laws.counit (F.toFunctor.obj X)).inv_even
  unit_inv_even X := preimage_grade hF hgrade _ (p.laws.counit (F.toFunctor.obj X)).hom_even
  counit_hom_even Y := (p.laws.counit Y).hom_even
  counit_inv_even Y := (p.laws.counit Y).inv_even

end RMod.Classification.SpanPreimages
