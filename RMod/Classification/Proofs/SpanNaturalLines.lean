import RMod.Classification.Instances.SpanNaturalIso
import RMod.Classification.Instances.SpanNaturalScaling
import RMod.Classification.Instances.SpanNaturalComposition
import RMod.Classification.Proofs.SpanNaturalCenter

/-!
# The parity and scalar line of a component comparison

Composing with a specified inverse turns comparisons into natural
endomorphisms of the fully faithful source functor. Its even center is
real and its odd supercenter vanishes. Consequently invertible
comparisons have a unique parity, and comparisons of that parity form
one real scalar line.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {S : C.data.Obj} {T : D.data.Obj}
  {F G : SpanSuperfunctor C D S T}

theorem SpanSuperfunctor.generator_id_ne_zero (hF : F.toFunctor.FullyFaithful)
    (hS : C.data.IsSimple S) : (𝟙 (F.data.obj (spanGenerator C S))) ≠ 0 := by
  intro hz
  have hm : F.toFunctor.map (𝟙 (spanGenerator C S)) = F.toFunctor.map 0 :=
    (F.toFunctor.map_id _).trans (hz.trans (F.toFunctor.map_zero _ _).symm)
  exact simple_id_ne_zero C.laws hS (congrArg (fun k => k.hom) (hF.map_injective hm))

namespace SpanHomogeneousNat

variable (hF : F.toFunctor.FullyFaithful)
  (hgrade : ∀ {X Y : HomogeneousSpanCategory C S} {b : ZMod 2} (f : X ⟶ Y),
    D.data.IsHomogeneous b (F.toFunctor.map f).hom ↔ C.data.IsHomogeneous b f.hom)

include hF hgrade

theorem degree_eq_zero_of_generator_ne_zero (hS : C.data.IsSimple S) {a : ZMod 2}
    (η : SpanHomogeneousNat F F a) (hη : η.data.app (spanGenerator C S) ≠ 0) : a = 0 := by
  rcases parity_cases a with rfl | rfl
  · rfl
  · exact False.elim (hη (congrArg (fun z : SpanHomogeneousNat F F 1 => z.data.app (spanGenerator C S))
      (odd_eq_zero hF hgrade hS η)))

theorem eq_zero_of_degree_ne_zero (hS : C.data.IsSimple S) {a : ZMod 2}
    (η : SpanHomogeneousNat F F a) (ha : a ≠ 0) : η = zero F F a := by
  rcases parity_cases a with rfl | rfl
  · exact False.elim (ha rfl)
  · exact odd_eq_zero hF hgrade hS η

end SpanHomogeneousNat

namespace SpanHomogeneousNatIso

variable (hF : F.toFunctor.FullyFaithful)
  (hgrade : ∀ {X Y : HomogeneousSpanCategory C S} {b : ZMod 2} (f : X ⟶ Y),
    D.data.IsHomogeneous b (F.toFunctor.map f).hom ↔ C.data.IsHomogeneous b f.hom)

include hF hgrade

omit hgrade in
theorem generator_hom_ne_zero (hS : C.data.IsSimple S) {a : ZMod 2}
    (η : SpanHomogeneousNatIso F G a) : η.data.app (spanGenerator C S) ≠ 0 := by
  intro hz
  apply SpanSuperfunctor.generator_id_ne_zero hF hS
  calc
    _ = η.data.app (spanGenerator C S) ≫ η.data.inv.app (spanGenerator C S) := (η.laws.hom_inv _).symm
    _ = 0 := by rw [hz]; simp

theorem parity_unique (hS : C.data.IsSimple S) {a b : ZMod 2}
    (η : SpanHomogeneousNatIso F G a) (θ : SpanHomogeneousNatIso F G b) : a = b := by
  let e := η.appIso (spanGenerator C S) ≪≫ (θ.appIso (spanGenerator C S)).symm
  have hne : (η.hom.comp θ.inverse).data.app (spanGenerator C S) ≠ 0 := by
    change e.hom ≠ 0
    intro hz
    apply SpanSuperfunctor.generator_id_ne_zero hF hS
    calc
      _ = e.hom ≫ e.inv := e.hom_inv_id.symm
      _ = 0 := by rw [hz]; simp
  have hab := SpanHomogeneousNat.degree_eq_zero_of_generator_ne_zero hF hgrade hS
    (η.hom.comp θ.inverse) hne
  calc
    a = (a + b) + b := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = b := by rw [hab, zero_add]

theorem comparison_eq_smul (hS : C.data.IsSimple S) {a : ZMod 2}
    (θ : SpanHomogeneousNatIso F G a) (η : SpanHomogeneousNat F G a) :
    ∃ r : ℝ, η = SpanHomogeneousNat.smul r θ.hom := by
  obtain ⟨r, hr⟩ := SpanHomogeneousNat.even_eq_scalar hF hgrade hS (η.compSameDegree θ.inverse)
  refine ⟨r, SpanHomogeneousNat.ext_generator _ _ ?_⟩
  let X := spanGenerator C S
  have hx := congrArg (fun z : SpanHomogeneousNat F F 0 => z.data.app X) hr
  change η.data.app X ≫ θ.data.inv.app X = r • 𝟙 (F.data.obj X) at hx
  change η.data.app X = r • θ.data.app X
  calc
    _ = (η.data.app X ≫ θ.data.inv.app X) ≫ θ.data.app X := by
      rw [Category.assoc, θ.laws.inv_hom, Category.comp_id]
    _ = _ := by rw [hx, Linear.smul_comp, Category.id_comp]

omit hgrade in
theorem comparison_smul_injective (hS : C.data.IsSimple S) {a : ZMod 2}
    (θ : SpanHomogeneousNatIso F G a) : Function.Injective (fun r : ℝ => SpanHomogeneousNat.smul r θ.hom) := by
  intro r s hrs
  have hh := congrArg (fun z : SpanHomogeneousNat F G a => z.data.app (spanGenerator C S)) hrs
  exact smul_left_injective ℝ (generator_hom_ne_zero hF hS θ) hh

theorem comparison_eq_unique_smul (hS : C.data.IsSimple S) {a : ZMod 2}
    (θ : SpanHomogeneousNatIso F G a) (η : SpanHomogeneousNat F G a) :
    ∃! r : ℝ, η = SpanHomogeneousNat.smul r θ.hom := by
  obtain ⟨r, hr⟩ := comparison_eq_smul hF hgrade hS θ η
  exact ⟨r, hr, fun s hs => comparison_smul_injective hF hS θ (hs.symm.trans hr)⟩

/-- The other homogeneous comparison space vanishes. -/
theorem comparison_other_degree_zero (hS : C.data.IsSimple S) {a b : ZMod 2}
    (θ : SpanHomogeneousNatIso F G a) (η : SpanHomogeneousNat F G b) (hba : b ≠ a) :
    η = SpanHomogeneousNat.zero F G b := by
  have hsum : b + a ≠ 0 := by
    intro hz
    apply hba
    calc
      b = (b + a) + a := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = a := by rw [hz, zero_add]
  have hz := SpanHomogeneousNat.eq_zero_of_degree_ne_zero hF hgrade hS (η.comp θ.inverse) hsum
  let X := spanGenerator C S
  have hx := congrArg (fun z : SpanHomogeneousNat F F (b + a) => z.data.app X) hz
  change η.data.app X ≫ θ.data.inv.app X = 0 at hx
  apply SpanHomogeneousNat.ext_generator
  change η.data.app X = 0
  calc
    _ = (η.data.app X ≫ θ.data.inv.app X) ≫ θ.data.app X := by
      rw [Category.assoc, θ.laws.inv_hom, Category.comp_id]
    _ = 0 := by rw [hx]; simp

/-- Invertible comparisons differ by a unique nonzero real scalar. -/
theorem comparison_eq_unique_unit_smul (hS : C.data.IsSimple S) {a : ZMod 2}
    (θ η : SpanHomogeneousNatIso F G a) :
    ∃! r : ℝˣ, η.hom = SpanHomogeneousNat.smul (r : ℝ) θ.hom := by
  obtain ⟨r, hr⟩ := comparison_eq_smul hF hgrade hS θ η.hom
  have hrne : r ≠ 0 := by
    intro hz
    have hx := congrArg (fun z : SpanHomogeneousNat F G a => z.data.app (spanGenerator C S)) hr
    change η.data.app (spanGenerator C S) = r • θ.data.app (spanGenerator C S) at hx
    rw [hz, zero_smul] at hx
    exact generator_hom_ne_zero hF hS η hx
  refine ⟨Units.mk0 r hrne, hr, ?_⟩
  intro s hs
  apply Units.ext
  exact comparison_smul_injective hF hS θ (hs.symm.trans hr)

end SpanHomogeneousNatIso
end RMod.Classification
