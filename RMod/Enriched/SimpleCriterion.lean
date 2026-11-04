import RMod.Enriched.SplitImages

/-! In a finite semisimple category, nonzero endomorphisms being monic
characterizes a nonzero simple object. This criterion also detects simplicity
across odd isomorphisms without assuming the graded Schur conclusion. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace RMod.EnrichedSupport
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

theorem simple_of_mono_end
    (hsemi : ∀ Y : C, ∃ (n : ℕ) (S : Fin n → C),
      (∀ i, Simple (S i)) ∧ Nonempty (Y ≅ ⨁ S))
    (Y : C) (hne : 𝟙 Y ≠ 0) (hm : ∀ f : Y ⟶ Y, f ≠ 0 → Mono f) : Simple Y := by
  obtain ⟨n, S, hS, ⟨e⟩⟩ := hsemi Y
  have hn : 0 < n := by
    by_contra h
    have hn : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    apply hne
    have hz : 𝟙 (⨁ S) = 0 := by
      apply biproduct.hom_ext
      intro j
      exact Fin.elim0 j
    calc
      𝟙 Y = e.hom ≫ 𝟙 (⨁ S) ≫ e.inv := by simp
      _ = 0 := by rw [hz]; simp
  let j : Fin n := ⟨0, hn⟩
  let i : S j ⟶ Y := biproduct.ι S j ≫ e.inv
  let p : Y ⟶ S j := e.hom ≫ biproduct.π S j
  have hip : i ≫ p = 𝟙 (S j) := by simp [i, p]
  have hpine : p ≫ i ≠ 0 := by
    intro h
    have hi : i = 0 := by
      calc
        i = (i ≫ p) ≫ i := by rw [hip]; simp
        _ = 0 := by rw [Category.assoc, h]; simp
    haveI := hS j
    exact (id_nonzero (S j)) (by rw [← hip, hi]; simp)
  haveI : Mono (p ≫ i) := hm _ hpine
  have hpi : p ≫ i = 𝟙 Y := by
    apply (cancel_mono (p ≫ i)).mp
    simp only [Category.assoc, ← Category.assoc i p i, hip, Category.id_comp]
  let iso : S j ≅ Y := ⟨i, p, hip, hpi⟩
  haveI := hS j
  exact Simple.of_iso iso.symm

end RMod.EnrichedSupport
