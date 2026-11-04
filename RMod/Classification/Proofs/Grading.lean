import RMod.Classification.Instances.LinearCategory
import RMod.Classification.Abstract.Reference
import Superfusion.Category.Supercategory

/-!
# Homogeneous inverses and intrinsic parity orbits

The inverse-degree theorem is reused from the existing supercategory library.
Its legacy interface is installed locally from the separate operations and
laws; it adds no choices or assumptions to the statement. The resulting
lemmas apply directly to the frozen raw predicates used by Challenge.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory

variable {D : WeaklyPointedSuperfusionData.{u, v}}
  (hD : WeaklyPointedSuperfusionLaws D)

include hD

/-- Any specified two-sided inverse has the same parity as its homogeneous map. -/
theorem homogeneous_inverse {X Y : D.Obj} {a : ZMod 2}
    (f : D.Hom X Y) (g : D.Hom Y X)
    (hfg : D.comp f g = D.id X) (hgf : D.comp g f = D.id Y)
    (hf : D.IsHomogeneous a f) : D.IsHomogeneous a g := by
  let C : WeaklyPointedSuperfusion := ⟨D, hD⟩
  letI : Superfusion.Category.Supercategory ℝ (LinearCategory C) :=
    { grade := LinearCategory.grade C
      isInternal_grade := LinearCategory.grade_isInternal C
      id_mem_even := hD.id_even
      comp_mem := hD.comp_grade }
  let e : @CategoryTheory.Iso (LinearCategory C) _ X Y := ⟨f, g, hfg, hgf⟩
  exact Superfusion.Category.inv_mem_homGrade_of_hom_mem ℝ e a hf

/-- The Schur law produces an isomorphism in the homogeneous orbit relation. -/
theorem homogeneous_schur {X Y : D.Obj} (hX : D.IsSimple X) (hY : D.IsSimple Y)
    {a : ZMod 2} (f : D.Hom X Y) (hf : D.IsHomogeneous a f) (hne : f ≠ D.zero) :
    D.HasHomogeneousIso a X Y := by
  obtain ⟨g, hfg, hgf⟩ := hD.graded_schur hX hY f hf hne
  exact ⟨f, g, hfg, hgf, hf, homogeneous_inverse hD f g hfg hgf hf⟩

/-- Simplicity excludes the zero object, as encoded by the original
even-monomorphism definition rather than an additional nonzero hypothesis. -/
theorem simple_id_ne_zero {X : D.Obj} (hX : D.IsSimple X) : D.id X ≠ D.zero := by
  have hm : D.IsEvenMono (D.id X) := by
    refine ⟨hD.id_even X, ?_⟩
    intro Z f g _ _ h
    simpa only [hD.comp_id] using h
  exact (hX X (D.id X) hm).mp
    ⟨hD.id_even X, D.id X, hD.id_even X, hD.comp_id _, hD.comp_id _⟩

/-! These two zero identities are Mathlib consequences of preadditivity. -/

theorem raw_zero_comp {X Y Z : D.Obj} (f : D.Hom Y Z) :
    D.comp (D.zero : D.Hom X Y) f = D.zero := by
  exact CategoryTheory.Limits.zero_comp (C := LinearCategory ⟨D, hD⟩)
    (X := X) (Y := Y) (Z := Z) (f := f)

theorem raw_comp_zero {X Y Z : D.Obj} (f : D.Hom X Y) :
    D.comp f (D.zero : D.Hom Y Z) = D.zero := by
  exact CategoryTheory.Limits.comp_zero (C := LinearCategory ⟨D, hD⟩)
    (X := X) (Y := Y) (Z := Z) (f := f)

theorem raw_finSum_zero {X Y : D.Obj} (n : ℕ) :
    D.finSum n (fun _ => (D.zero : D.Hom X Y)) = D.zero := by
  rw [LinearCategory.finSum_eq_sum ⟨D, hD⟩ (X := X) (Y := Y)]
  change (∑ _ : Fin n, (0 : @Quiver.Hom (LinearCategory ⟨D, hD⟩) _ X Y)) = 0
  exact Finset.sum_const_zero

theorem raw_finSum_comp {X Y Z : D.Obj} (n : ℕ) (f : Fin n → D.Hom X Y)
    (g : D.Hom Y Z) :
    D.comp (D.finSum n f) g = D.finSum n (fun i => D.comp (f i) g) := by
  rw [LinearCategory.finSum_eq_sum ⟨D, hD⟩ (X := X) (Y := Y),
    LinearCategory.finSum_eq_sum ⟨D, hD⟩ (X := X) (Y := Z)]
  exact Preadditive.sum_comp (C := LinearCategory ⟨D, hD⟩) Finset.univ f g

theorem raw_comp_finSum {X Y Z : D.Obj} (n : ℕ) (f : D.Hom X Y)
    (g : Fin n → D.Hom Y Z) :
    D.comp f (D.finSum n g) = D.finSum n (fun i => D.comp f (g i)) := by
  rw [LinearCategory.finSum_eq_sum ⟨D, hD⟩ (X := Y) (Y := Z),
    LinearCategory.finSum_eq_sum ⟨D, hD⟩ (X := X) (Y := Z)]
  exact Preadditive.comp_sum (C := LinearCategory ⟨D, hD⟩) Finset.univ f g

/-! Homogeneous isomorphisms compose with the sum of their degrees. -/

theorem homogeneousIso_refl (X : D.Obj) : D.HasHomogeneousIso 0 X X :=
  ⟨D.id X, D.id X, hD.comp_id _, hD.comp_id _, hD.id_even X, hD.id_even X⟩

omit hD in
theorem homogeneousIso_symm {X Y : D.Obj} {a : ZMod 2}
    (h : D.HasHomogeneousIso a X Y) : D.HasHomogeneousIso a Y X := by
  obtain ⟨f, g, hfg, hgf, hf, hg⟩ := h
  exact ⟨g, f, hgf, hfg, hg, hf⟩

theorem homogeneousIso_trans {X Y Z : D.Obj} {a b : ZMod 2}
    (h : D.HasHomogeneousIso a X Y) (k : D.HasHomogeneousIso b Y Z) :
    D.HasHomogeneousIso (a + b) X Z := by
  obtain ⟨f, g, hfg, hgf, hf, hg⟩ := h
  obtain ⟨p, q, hpq, hqp, hp, hq⟩ := k
  refine ⟨D.comp f p, D.comp q g, ?_, ?_, hD.comp_grade _ _ hf hp, ?_⟩
  · rw [hD.comp_assoc, ← hD.comp_assoc p, hpq, hD.id_comp, hfg]
  · rw [hD.comp_assoc, ← hD.comp_assoc g, hgf, hD.id_comp, hqp]
  · simpa only [WeaklyPointedSuperfusionData.IsHomogeneous, add_comm]
      using hD.comp_grade _ _ hq hg

end RMod.Classification

namespace RMod.Classification.SameParityOrbit

variable {D : WeaklyPointedSuperfusionData.{0, 0}}
  (hD : WeaklyPointedSuperfusionLaws D)

include hD

theorem refl (X : D.Obj) : SameParityOrbit D X X := ⟨0, homogeneousIso_refl hD X⟩

omit hD in
theorem symm {X Y : D.Obj} (h : SameParityOrbit D X Y) : SameParityOrbit D Y X := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, homogeneousIso_symm ha⟩

theorem trans {X Y Z : D.Obj} (h : SameParityOrbit D X Y) (k : SameParityOrbit D Y Z) :
    SameParityOrbit D X Z := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := k
  exact ⟨a + b, homogeneousIso_trans hD ha hb⟩

/-- The relation used by the classification really is an equivalence relation. -/
theorem equivalence : Equivalence (SameParityOrbit D) :=
  ⟨refl hD, symm, trans hD⟩

/-- Clifford type is invariant under homogeneous isomorphism, directly from
the finite-amplification definition, without the reference property P. -/
theorem hasBWType_iff {X Y : D.Obj} (h : SameParityOrbit D X Y) (r : ZMod 8) :
    HasBWType D X r ↔ HasBWType D Y r := by
  constructor
  · rintro ⟨n, S, Z, hn, hS, hd, he⟩
    exact ⟨n, S, Z, hn, fun i => trans hD (symm h) (hS i), hd, he⟩
  · rintro ⟨n, S, Z, hn, hS, hd, he⟩
    exact ⟨n, S, Z, hn, fun i => trans hD h (hS i), hd, he⟩

end RMod.Classification.SameParityOrbit
