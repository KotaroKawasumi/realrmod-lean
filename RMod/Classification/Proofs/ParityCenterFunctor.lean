import RMod.Classification.Instances.ParityCenterFunctor
import RMod.Classification.Proofs.CenterParityMultiplication

/-!
# Monoidal laws of the central parity-factor functor

The tensorators are the specified multiplication isomorphisms. Their
proved associativity and normalized unit cases give Mathlib's monoidal
functor interface, including inverse-tensorator coherence supplied by
the library. This does not assert that the functor is braided: the odd
self-crossing is the nontrivial sign used in the parity pentagon.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory MonoidalCategory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v}) (p : PiData C.data) (hp : PiLaws C.data p)

theorem parityCenterFunctor_map {X Y : Discrete (Multiplicative (ZMod 2))} (f : X ⟶ Y) :
    (parityCenterFunctor C p hp).map f =
      eqToHom (congrArg (fun a => factorCenter C p hp a.toAdd) (Discrete.eq_of_hom f)) := by
  obtain ⟨x⟩ := X
  obtain ⟨y⟩ := Y
  obtain ⟨⟨he⟩⟩ := f
  cases he
  rfl

noncomputable def parityCenterCoreMonoidal : (parityCenterFunctor C p hp).CoreMonoidal where
  εIso := Iso.refl _
  μIso X Y := factorMultiplyCenterIso C p hp X.as.toAdd Y.as.toAdd
  μIso_hom_natural_left {X Y} f Z := by
    obtain ⟨x⟩ := X
    obtain ⟨y⟩ := Y
    obtain ⟨⟨he⟩⟩ := f
    cases he
    simp [parityCenterFunctor, Discrete.functor]
  μIso_hom_natural_right Z {X Y} f := by
    obtain ⟨x⟩ := X
    obtain ⟨y⟩ := Y
    obtain ⟨⟨he⟩⟩ := f
    cases he
    simp [parityCenterFunctor, Discrete.functor]
  associativity X Y Z := by
    rw [parityCenterFunctor_map]
    have he := factorMultiplyCenter_assoc C p hp X.as.toAdd Y.as.toAdd Z.as.toAdd
    simp only [tensorHom_id, id_tensorHom] at he
    exact he
  left_unitality X := by
    rw [parityCenterFunctor_map]
    obtain ⟨x⟩ := X
    rcases parity_cases x.toAdd with h | h
    · have he : x = 1 := congrArg Multiplicative.ofAdd h
      subst x
      change (λ_ (factorCenter C p hp 0)).hom =
        (𝟙 _ ▷ factorCenter C p hp 0) ≫ (factorMultiplyCenterIso C p hp 0 0).hom ≫ 𝟙 _
      simp only [id_whiskerRight, Category.id_comp, Category.comp_id]
      rfl
    · have he : x = Multiplicative.ofAdd (1 : ZMod 2) := congrArg Multiplicative.ofAdd h
      subst x
      change (λ_ (factorCenter C p hp 1)).hom =
        (𝟙 _ ▷ factorCenter C p hp 1) ≫ (factorMultiplyCenterIso C p hp 0 1).hom ≫ 𝟙 _
      simp only [id_whiskerRight, Category.id_comp, Category.comp_id]
      rfl
  right_unitality X := by
    rw [parityCenterFunctor_map]
    obtain ⟨x⟩ := X
    rcases parity_cases x.toAdd with h | h
    · have he : x = 1 := congrArg Multiplicative.ofAdd h
      subst x
      change (ρ_ (factorCenter C p hp 0)).hom =
        (factorCenter C p hp 0 ◁ 𝟙 _) ≫ (factorMultiplyCenterIso C p hp 0 0).hom ≫ 𝟙 _
      simp only [whiskerLeft_id, Category.id_comp, Category.comp_id]
      apply Center.ext
      apply WideSubcategory.hom_ext
      exact (unitors_hom_equal C.laws).symm
    · have he : x = Multiplicative.ofAdd (1 : ZMod 2) := congrArg Multiplicative.ofAdd h
      subst x
      change (ρ_ (factorCenter C p hp 1)).hom =
        (factorCenter C p hp 1 ◁ 𝟙 _) ≫ (factorMultiplyCenterIso C p hp 1 0).hom ≫ 𝟙 _
      simp only [whiskerLeft_id, Category.id_comp, Category.comp_id]
      rfl

noncomputable instance parityCenterFunctorMonoidal : (parityCenterFunctor C p hp).Monoidal :=
  (parityCenterCoreMonoidal C p hp).toMonoidal

theorem parityCenterFunctor_tensorHom (a b : ZMod 2) :
    (Functor.LaxMonoidal.μ (parityCenterFunctor C p hp)
      (Discrete.mk (Multiplicative.ofAdd a)) (Discrete.mk (Multiplicative.ofAdd b))).f.hom =
      (p.multiplyFactors a b).hom := rfl

theorem parityCenterFunctor_tensorInv (a b : ZMod 2) :
    (Functor.OplaxMonoidal.δ (parityCenterFunctor C p hp)
      (Discrete.mk (Multiplicative.ofAdd a)) (Discrete.mk (Multiplicative.ofAdd b))).f.hom =
      (p.multiplyFactors a b).inv :=
  factorMultiplyCenterIso_inv C p hp a b

end RMod.Classification
