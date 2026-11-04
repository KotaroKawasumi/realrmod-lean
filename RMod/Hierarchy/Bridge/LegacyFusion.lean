import RMod.Hierarchy.Bridge.LegacyFinite

/-!
# Fusion and split-unit predicates for extracted data

The raw predicates use the same total morphisms and homogeneous supports.
The finite-orbit and Schur conditions therefore transfer directly, while
the unit algebra equivalence identifies every endomorphism with a scalar.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy

theorem legacyFiniteSimples (A : FusionPiSupercategory) :
    ∃ (n : ℕ) (S : Fin n → (toOldData A.toMonoidalPiSupercategory.monoidal).Obj),
      (∀ i, (toOldData A.toMonoidalPiSupercategory.monoidal).IsSimple (S i)) ∧
      ∀ X, (toOldData A.toMonoidalPiSupercategory.monoidal).IsSimple X →
        ∃ i a, (toOldData A.toMonoidalPiSupercategory.monoidal).HasHomogeneousIso a X (S i) := by
  obtain ⟨n, S, hS, h⟩ := A.finite_simples
  refine ⟨n, fun i => S i, fun i => (legacySimple_iff _ _).mpr (hS i), ?_⟩
  intro X hX
  obtain ⟨i, a, e, he, hei⟩ := h (evenObj _ X) ((legacySimple_iff _ _).mp hX)
  exact ⟨i, a, e.hom, e.inv, e.hom_inv_id, e.inv_hom_id, he, hei⟩

theorem legacyGradedSchur (A : FusionPiSupercategory)
    {X Y : (toOldData A.toMonoidalPiSupercategory.monoidal).Obj}
    (hX : (toOldData A.toMonoidalPiSupercategory.monoidal).IsSimple X)
    (hY : (toOldData A.toMonoidalPiSupercategory.monoidal).IsSimple Y)
    {a : ZMod 2} (f : (toOldData A.toMonoidalPiSupercategory.monoidal).Hom X Y)
    (hf : (toOldData A.toMonoidalPiSupercategory.monoidal).IsHomogeneous a f)
    (hf₀ : f ≠ (toOldData A.toMonoidalPiSupercategory.monoidal).zero) :
    (toOldData A.toMonoidalPiSupercategory.monoidal).IsIso f := by
  let S := A.toMonoidalPiSupercategory.monoidal.super
  let f' : totalObj S X ⟶ totalObj S Y := f
  letI : IsIso f' := A.graded_schur (evenObj S X) (evenObj S Y)
    ((legacySimple_iff _ _).mp hX) ((legacySimple_iff _ _).mp hY) a f hf hf₀
  exact ⟨inv f', IsIso.hom_inv_id f', IsIso.inv_hom_id f'⟩

theorem legacyUnitScalarInjective (A : WeaklyPointedFusionPiSupercategory)
    (r s : ℝ)
    (h : (toOldData A.toMonoidalPiSupercategory.monoidal).smul r
      ((toOldData A.toMonoidalPiSupercategory.monoidal).id A.data.monoidal.unit) =
      (toOldData A.toMonoidalPiSupercategory.monoidal).smul s
      ((toOldData A.toMonoidalPiSupercategory.monoidal).id A.data.monoidal.unit)) : r = s := by
  obtain ⟨e⟩ := A.splitUnit
  have he := congrArg e h
  change e (r • (1 : End (totalObj A.toMonoidalPiSupercategory.monoidal.super A.data.monoidal.unit))) = e (s • 1) at he
  simpa only [map_smul, map_one, smul_eq_mul, mul_one] using he

theorem legacyUnitScalarSurjective (A : WeaklyPointedFusionPiSupercategory)
    (f : (toOldData A.toMonoidalPiSupercategory.monoidal).Hom A.data.monoidal.unit
      A.data.monoidal.unit) :
    ∃ r : ℝ, (toOldData A.toMonoidalPiSupercategory.monoidal).smul r
      ((toOldData A.toMonoidalPiSupercategory.monoidal).id A.data.monoidal.unit) = f := by
  obtain ⟨e⟩ := A.splitUnit
  refine ⟨e f, e.injective ?_⟩
  change e (e f • (1 : End (totalObj A.toMonoidalPiSupercategory.monoidal.super A.data.monoidal.unit))) = e f
  simp only [map_smul, map_one, smul_eq_mul, mul_one]

end RMod.Legacy.Hierarchy
