import RMod.Classification.Instances.Functors

/-!
# The original simplicity predicate and Mathlib simplicity

Even monomorphisms and even isomorphisms in the raw statement are precisely
monomorphisms and isomorphisms in the existing even subcategory. Thus the
immutable simplicity definition agrees with Mathlib `Simple`. Equivalence
invariance is then proved using Mathlib's preservation of monomorphisms,
reflection of isomorphisms, and the even natural unit.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u₁, v₁})

theorem even_hom_eq_zero_iff {X Y : EvenSubcategory ℝ (LinearCategory C)} (f : X ⟶ Y) :
    f.hom = C.data.zero ↔ f = 0 := by
  constructor
  · intro h
    apply WideSubcategory.hom_ext
    exact h
  · intro h
    exact congrArg (fun g => g.hom) h

theorem even_mono_iff {X Y : EvenSubcategory ℝ (LinearCategory C)} (f : X ⟶ Y) :
    Mono f ↔ C.data.IsEvenMono f.hom := by
  constructor
  · intro hm
    letI := hm
    refine ⟨f.property, fun Z g h hg hh he => ?_⟩
    let g' : evenObj ℝ (LinearCategory C) Z ⟶ X := ⟨g, hg⟩
    let h' : evenObj ℝ (LinearCategory C) Z ⟶ X := ⟨h, hh⟩
    have he' : g' ≫ f = h' ≫ f := WideSubcategory.hom_ext _ he
    exact congrArg (fun k => k.hom) ((cancel_mono f).mp he')
  · intro hm
    refine ⟨fun {Z} g h he => ?_⟩
    apply WideSubcategory.hom_ext
    exact hm.2 Z.obj g.hom h.hom g.property h.property (congrArg (fun k => k.hom) he)

theorem even_isIso_iff {X Y : EvenSubcategory ℝ (LinearCategory C)} (f : X ⟶ Y) :
    IsIso f ↔ C.data.IsEvenIso f.hom := by
  constructor
  · rintro ⟨g, hfg, hgf⟩
    exact ⟨f.property, g.hom, g.property,
      congrArg (fun k => k.hom) hfg, congrArg (fun k => k.hom) hgf⟩
  · rintro ⟨_, g, hg, hfg, hgf⟩
    exact ⟨⟨g, hg⟩, WideSubcategory.hom_ext _ hfg, WideSubcategory.hom_ext _ hgf⟩

theorem isSimple_iff_evenSimple (X : C.data.Obj) :
    C.data.IsSimple X ↔ Simple (evenObj ℝ (LinearCategory C) X) := by
  constructor
  · intro hX
    refine ⟨fun {Y} f hm => ?_⟩
    exact (even_isIso_iff C f).trans
      ((hX Y.obj f.hom ((even_mono_iff C f).mp hm)).trans
        (not_congr (even_hom_eq_zero_iff C f)))
  · intro hX Y f hm
    letI := hX
    let f' : evenObj ℝ (LinearCategory C) Y ⟶ evenObj ℝ (LinearCategory C) X := ⟨f, hm.1⟩
    letI : Mono f' := (even_mono_iff C f').mpr hm
    exact (even_isIso_iff C f').symm.trans
      ((Simple.mono_isIso_iff_nonzero f').trans
        (not_congr (even_hom_eq_zero_iff C f')).symm)

private theorem simple_map_of_equivalence
    {A : Type u₁} [Category.{v₁} A] [Limits.HasZeroMorphisms A]
    {B : Type u₂} [Category.{v₂} B] [Limits.HasZeroMorphisms B]
    (E : A ≌ B) [E.inverse.PreservesZeroMorphisms] (X : A) [Simple X] :
    Simple (E.functor.obj X) := by
  let η : X ≅ E.inverse.obj (E.functor.obj X) := E.unitIso.app X
  haveI : Simple (E.inverse.obj (E.functor.obj X)) := Simple.of_iso η.symm
  refine ⟨fun f _ => ?_⟩
  exact (isIso_iff_of_reflects_iso f E.inverse).symm.trans
    ((Simple.mono_isIso_iff_nonzero (E.inverse.map f)).trans
      (not_congr (Functor.map_eq_zero_iff E.inverse)))

namespace MonoidalSuperequivalence

variable {C} {D : WeaklyPointedSuperfusion.{u₂, v₂}} (E : MonoidalSuperequivalence C D)

theorem isSimple_map_iff (X : C.data.Obj) :
    D.data.IsSimple (E.data.forward.obj X) ↔ C.data.IsSimple X := by
  rw [isSimple_iff_evenSimple, isSimple_iff_evenSimple]
  constructor
  · intro h
    let X' := evenObj ℝ (LinearCategory C) X
    haveI : Simple (E.evenEquivalence.functor.obj X') := h
    haveI : Simple (E.evenEquivalence.inverse.obj (E.evenEquivalence.functor.obj X')) :=
      simple_map_of_equivalence E.evenEquivalence.symm (E.evenEquivalence.functor.obj X')
    let η : X' ≅ E.evenEquivalence.inverse.obj (E.evenEquivalence.functor.obj X') :=
      E.evenEquivalence.unitIso.app X'
    exact Simple.of_iso η
  · intro h
    letI := h
    exact simple_map_of_equivalence E.evenEquivalence (evenObj ℝ (LinearCategory C) X)

theorem isSimple_backward_map_iff (Y : D.data.Obj) :
    C.data.IsSimple (E.data.backward.obj Y) ↔ D.data.IsSimple Y := by
  rw [isSimple_iff_evenSimple, isSimple_iff_evenSimple]
  constructor
  · intro h
    let Y' := evenObj ℝ (LinearCategory D) Y
    haveI : Simple (E.evenEquivalence.inverse.obj Y') := h
    haveI : Simple (E.evenEquivalence.functor.obj (E.evenEquivalence.inverse.obj Y')) :=
      simple_map_of_equivalence E.evenEquivalence (E.evenEquivalence.inverse.obj Y')
    let ε : E.evenEquivalence.functor.obj (E.evenEquivalence.inverse.obj Y') ≅ Y' :=
      E.evenEquivalence.counitIso.app Y'
    exact Simple.of_iso ε.symm
  · intro h
    letI := h
    exact simple_map_of_equivalence E.evenEquivalence.symm (evenObj ℝ (LinearCategory D) Y)

end MonoidalSuperequivalence
end RMod.Classification
