import Mathlib.CategoryTheory.Idempotents.Basic

/-! A fully faithful functor from an idempotent-complete category has
image closed under retracts. Thus showing that every target object is a
retract of an image object suffices for essential surjectivity. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [Category C] [Category D] [IsIdempotentComplete C]
  (F : C ⥤ D) [F.Full] [F.Faithful]

theorem image_of_retract {X : C} {W : D} (r : Retract W (F.obj X)) :
    ∃ Y : C, Nonempty (F.obj Y ≅ W) := by
  let p : X ⟶ X := F.preimage (r.r ≫ r.i)
  have hp : p ≫ p = p := by
    apply F.map_injective
    simp only [CategoryTheory.Functor.map_comp, p, F.map_preimage]
    simp only [assoc, ← assoc r.i r.r, r.retract, Category.id_comp]
  obtain ⟨Y, i, e, hi, he⟩ := IsIdempotentComplete.idempotents_split X p hp
  have hmap : F.map e ≫ F.map i = r.r ≫ r.i := by
    rw [← F.map_comp, he]
    exact F.map_preimage _
  refine ⟨Y, ⟨{
    hom := F.map i ≫ r.r
    inv := r.i ≫ F.map e
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · calc
      _ = F.map i ≫ (F.map e ≫ F.map i) ≫ F.map e := by simp only [assoc, hmap]
      _ = (F.map i ≫ F.map e) ≫ (F.map i ≫ F.map e) := by simp only [assoc]
      _ = 𝟙 _ := by rw [← F.map_comp, hi, F.map_id, Category.id_comp]
  · simp only [assoc, ← assoc (F.map e) (F.map i), hmap]
    simp only [← assoc, r.retract, Category.id_comp]

theorem essSurj_of_retracts (h : ∀ W : D, ∃ X : C, Nonempty (Retract W (F.obj X))) :
    F.EssSurj where
  mem_essImage W := by
    obtain ⟨X, ⟨r⟩⟩ := h W
    exact image_of_retract F r

end RMod.BrundanEllis.Stacking
