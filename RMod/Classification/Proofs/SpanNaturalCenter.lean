import RMod.Classification.Proofs.SpanNaturalExt
import RMod.Classification.Instances.SpanNaturalScalars
import RMod.Classification.Proofs.EndSuperCentral
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Natural endomorphisms lie in the generator supercenter

Full faithfulness lifts a natural endomorphism at the generator to its
endomorphism algebra. Signed naturality against every homogeneous
generator endomorphism is exactly the supercentrality equation. This is
the algebraic input for the scalar and parity uniqueness of comparisons.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanHomogeneousNat

open CategoryTheory Superfusion

attribute [local implicit_reducible] CategoryTheory.End

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F : SpanSuperfunctor C D S T} {a : ZMod 2}
  (hF : F.toFunctor.FullyFaithful) (η : SpanHomogeneousNat F F a)

theorem generator_preimage_supercentral :
    IsSupercentral (Category.endGrading (K := ℝ) (C := LinearCategory C) S) a
      (hF.preimage (η.data.app (spanGenerator C S))).hom := by
  intro j b hb
  rw [← Category.koszulSign_smul_eq_sgn_zsmul ℝ a j]
  let B : spanGenerator C S ⟶ spanGenerator C S := ObjectProperty.homMk b
  let Z : spanGenerator C S ⟶ spanGenerator C S := hF.preimage (η.data.app (spanGenerator C S))
  have h : B ≫ Z = ((-1 : ℝ) ^ (a * j).val) • (Z ≫ B) := by
    apply hF.map_injective
    change F.toFunctor.map (B ≫ hF.preimage (η.data.app (spanGenerator C S))) =
      F.toFunctor.map (((-1 : ℝ) ^ (a * j).val) •
        (hF.preimage (η.data.app (spanGenerator C S)) ≫ B))
    rw [Functor.map_comp, Functor.map_smul, Functor.map_comp, hF.map_preimage]
    exact η.laws.naturality B hb
  exact congrArg (fun f => f.hom) h

variable (hgrade : ∀ {X Y : HomogeneousSpanCategory C S} {b : ZMod 2} (f : X ⟶ Y),
  D.data.IsHomogeneous b (F.toFunctor.map f).hom ↔ C.data.IsHomogeneous b f.hom)

include hF hgrade

theorem generator_preimage_grade :
    C.data.IsHomogeneous a (hF.preimage (η.data.app (spanGenerator C S))).hom := by
  apply (hgrade _).mp
  rw [hF.map_preimage]
  exact η.laws.grade _

/-- Signed odd naturality forces the generator value, and hence every component, to vanish. -/
theorem odd_eq_zero (hS : C.data.IsSimple S) (θ : SpanHomogeneousNat F F 1) : θ = zero F F 1 := by
  have hz := odd_supercentral_eq_zero C S hS
    (hF.preimage (θ.data.app (spanGenerator C S))).hom
    (generator_preimage_grade hF θ hgrade) (generator_preimage_supercentral hF θ)
  have hh : hF.preimage (θ.data.app (spanGenerator C S)) = 0 := ObjectProperty.hom_ext _ hz
  apply ext_generator
  have hm := congrArg F.toFunctor.map hh
  rw [hF.map_preimage, Functor.map_zero] at hm
  exact hm

/-- The even natural endomorphism algebra of a fully faithful component functor is real. -/
theorem even_eq_scalar (hS : C.data.IsSimple S) (θ : SpanHomogeneousNat F F 0) :
    ∃ r : ℝ, θ = scalar F r := by
  let z : @End (LinearCategory C) _ S := (hF.preimage (θ.data.app (spanGenerator C S))).hom
  have hz := generator_preimage_grade hF θ hgrade
  have hc := even_supercentral_mem_center C S z (generator_preimage_supercentral hF θ)
  obtain ⟨r, hr⟩ := even_central_eq_scalar_of_weaklyInvertible C S
    (simple_id_ne_zero C.laws hS) (C.laws.weakly_pointed S hS) z hz hc
  have hh : hF.preimage (θ.data.app (spanGenerator C S)) = r • 𝟙 (spanGenerator C S) :=
    ObjectProperty.hom_ext _ hr
  refine ⟨r, ext_generator θ (scalar F r) ?_⟩
  have hm := congrArg F.toFunctor.map hh
  rw [hF.map_preimage, Functor.map_smul] at hm
  exact hm.trans (congrArg (fun f => r • f) (F.toFunctor.map_id (spanGenerator C S)))

omit hgrade in
theorem scalar_injective (hS : C.data.IsSimple S) : Function.Injective (scalar F) := by
  have hi : (𝟙 (F.toFunctor.obj (spanGenerator C S))) ≠ 0 := by
    intro hz
    have h : (𝟙 (spanGenerator C S)) = 0 := by
      apply hF.map_injective
      rw [F.toFunctor.map_id, Functor.map_zero]
      exact hz
    exact simple_id_ne_zero C.laws hS (congrArg (fun f => f.hom) h)
  intro r s h
  have hh := congrArg (fun η : SpanHomogeneousNat F F 0 => η.data.app (spanGenerator C S)) h
  change r • 𝟙 (F.toFunctor.obj (spanGenerator C S)) =
    s • 𝟙 (F.toFunctor.obj (spanGenerator C S)) at hh
  exact smul_left_injective ℝ hi hh

theorem even_eq_unique_scalar (hS : C.data.IsSimple S) (θ : SpanHomogeneousNat F F 0) :
    ∃! r : ℝ, θ = scalar F r := by
  obtain ⟨r, hr⟩ := even_eq_scalar hF hgrade hS θ
  exact ⟨r, hr, fun s hs => scalar_injective hF hS (hs.symm.trans hr)⟩

end RMod.Classification.SpanHomogeneousNat
