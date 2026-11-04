import RMod.BrundanEllis.StackingSemisimpleTransfer
import RMod.Enriched.SplitImages
import Mathlib.CategoryTheory.Preadditive.Schur

/-! In a finite semisimple category, monomorphisms split and a simple
retract of a finite sum is already a retract of one summand. This reduction
is useful for checking weak invertibility only on paired generators. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
attribute [local instance] Abelian.hasFiniteBiproducts
namespace RMod.BrundanEllis.Stacking
variable {C : Type} [Category C] [Abelian C]
  (h : ∀ X : C, ∃ (n : ℕ) (S : Fin n → C),
    (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S))

include h

theorem semisimple_mono_retract {X Y : C} (f : X ⟶ Y) [Mono f] : Nonempty (Retract X Y) := by
  have hs : RMod.EnrichedSupport.HasSplitImage f := by
    apply RMod.EnrichedSupport.split_images_of_semisimple h
    intro S T hS hT g hg
    letI := hS
    letI := hT
    exact isIso_of_hom_simple hg
  obtain ⟨J, p, i, s, r, hp, hi, hf⟩ := hs
  have hps : p ≫ s = 𝟙 X := by
    apply (cancel_mono f).mp
    rw [← hf]
    simp only [Category.id_comp, assoc, ← assoc s p i, hp]
  refine ⟨{ i := f, r := r ≫ s, retract := ?_ }⟩
  rw [← hf]
  rw [assoc, ← assoc i r s, hi, Category.id_comp, hps]

/-- A simple retract cannot require several summands to support its identity. -/
theorem simple_retract_summand {n : ℕ} (Y : Fin n → C) {X : C} [Simple X]
    (r : Retract X (⨁ Y)) : ∃ j, Nonempty (Retract X (Y j)) := by
  classical
  have hex : ∃ j, r.i ≫ biproduct.π Y j ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    have hi : r.i = 0 := by
      apply biproduct.hom_ext
      intro j
      simpa only [zero_comp] using hzero j
    have hid : 𝟙 X = 0 := by
      rw [← r.retract, hi, zero_comp]
    exact id_nonzero X hid
  obtain ⟨j, hj⟩ := hex
  haveI : Mono (r.i ≫ biproduct.π Y j) := mono_of_nonzero_from_simple hj
  exact ⟨j, semisimple_mono_retract h (r.i ≫ biproduct.π Y j)⟩

end RMod.BrundanEllis.Stacking
